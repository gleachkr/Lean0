//! The statement checker (`lean0 check`): do the generated `.mm0` statements say what the
//! export's declarations say?
//!
//! The certificate proves its `.mm0` statements; this ties them to Lean. It reads the
//! generated statements (the files of all parts, in order) and, for each declaration of the
//! export, finds the MM0 term standing for it (named in its doc comment, "Lean ... `NAME`."),
//! the statements that give its type (`ty G (c us) T` for a definition or theorem, the
//! `constDF` axiom `deq G (c us) (c us2) T` for an opaque constant), and for a definition its
//! body. Each of those is translated back into a Lean expression and compared with the
//! export: up to binder names and styles, with `let`s inlined and string literals expanded,
//! as the translation does. Every theorem must have a proved (not assumed) type statement.
//!
//! Like the rest of this crate it is independent of the generator: it parses the `.mm0` text
//! itself, for exactly the forms lean0 writes. What it does not check: the generated axioms
//! (inductive, quotient and literal rules; audit §4, §5), and that the certificate proves the
//! statements (the verifiers' job).

use nanoda_lib::env::Declar;
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::name::Name;
use nanoda_lib::util::{ExportFile, ExprPtr, LevelPtr, NamePtr, TcCtx};
use num_bigint::BigUint;
use std::collections::HashMap;

/// An MM0 expression as written: a head and its arguments (a bare identifier has none).
#[derive(Debug)]
pub struct M {
    head: String,
    args: Vec<M>,
}

fn parse_math(s: &str) -> Result<M, String> {
    let spaced = s.replace('(', " ( ").replace(')', " ) ");
    let toks: Vec<&str> = spaced.split_whitespace().collect();
    let mut i = 0;
    let m = parse_app(&toks, &mut i)?;
    if i != toks.len() {
        return Err(format!("trailing tokens in `{s}`"))
    }
    Ok(m)
}

/// `head arg*` up to a closing parenthesis or the end.
fn parse_app(toks: &[&str], i: &mut usize) -> Result<M, String> {
    let head = match toks.get(*i) {
        Some(&"(") | Some(&")") | None => return Err("expected an identifier".into()),
        Some(t) => t.to_string(),
    };
    *i += 1;
    let mut args = Vec::new();
    while let Some(&t) = toks.get(*i) {
        match t {
            ")" => break,
            "(" => {
                *i += 1;
                args.push(parse_app(toks, i)?);
                if toks.get(*i) != Some(&")") {
                    return Err("unbalanced parentheses".into())
                }
                *i += 1;
            }
            t => {
                args.push(M { head: t.to_string(), args: Vec::new() });
                *i += 1;
            }
        }
    }
    Ok(M { head, args })
}

/// A generated statement: kind (`term`, `def`, `axiom`, `theorem`), name, binders (name, sort),
/// hypotheses and conclusion (or a def's body), and its doc comment.
#[derive(Debug)]
pub struct Stmt {
    kind: String,
    name: String,
    binders: Vec<(String, String)>,
    hyps: Vec<M>,
    concl: Option<M>,
    doc: String,
}

/// Parse the statements of a generated `.mm0` file (its `import` line is skipped).
pub fn parse_mm0(text: &str) -> Result<Vec<Stmt>, String> {
    let mut out = Vec::new();
    let mut doc = String::new();
    let mut rest = text;
    loop {
        rest = rest.trim_start();
        if rest.is_empty() {
            return Ok(out)
        }
        if let Some(r) = rest.strip_prefix("--|") {
            let (line, r) = r.split_once('\n').unwrap_or((r, ""));
            doc.push_str(line.trim());
            rest = r;
            continue
        }
        if rest.starts_with("--") {
            rest = rest.split_once('\n').map_or("", |x| x.1);
            continue
        }
        // a statement ends at the first `;` outside `$ ... $`
        let mut in_math = false;
        let end = rest.char_indices().find(|&(_, c)| {
            if c == '$' {
                in_math = !in_math;
            }
            c == ';' && !in_math
        });
        let Some((end, _)) = end else { return Err("unterminated statement".into()) };
        let st = &rest[..end];
        rest = &rest[end + 1..];
        let d = std::mem::take(&mut doc);
        if st.starts_with("import ") {
            continue
        }
        out.push(parse_stmt(st, d)?);
    }
}

fn parse_stmt(st: &str, doc: String) -> Result<Stmt, String> {
    let (kind, r) = st.split_once(' ').ok_or_else(|| format!("bad statement `{st}`"))?;
    if !matches!(kind, "term" | "def" | "axiom" | "theorem") {
        return Err(format!("unexpected statement kind `{kind}`"))
    }
    let r = r.trim_start();
    let name_end = r.find(|c: char| c == ' ' || c == '(' || c == ':').ok_or("bad statement")?;
    let name = r[..name_end].to_string();
    let mut r = r[name_end..].trim_start();
    let mut binders = Vec::new();
    while let Some(b) = r.strip_prefix('(') {
        let (inner, rr) = b.split_once(')').ok_or("bad binder")?;
        let (vars, sort) = inner.split_once(':').ok_or("bad binder")?;
        for v in vars.split_whitespace() {
            binders.push((v.to_string(), sort.trim().to_string()));
        }
        r = rr.trim_start();
    }
    let r = r.strip_prefix(':').ok_or_else(|| format!("{name}: expected `:`"))?.trim();
    let maths: Vec<&str> = r.split('$').collect();
    let (hyps, concl) = match kind {
        "term" => (Vec::new(), None),
        "def" => match r.split_once('=') {
            None => (Vec::new(), None),
            Some((_, body)) => (Vec::new(), Some(parse_math(body.trim().trim_matches('$').trim())?)),
        },
        _ => {
            // `$ h1 $ > ... $ c $`: the math blocks are the odd pieces
            let mut ms: Vec<M> = maths.iter().skip(1).step_by(2).map(|m| parse_math(m.trim())).collect::<Result<_, _>>()?;
            let c = ms.pop().ok_or_else(|| format!("{name}: no conclusion"))?;
            (ms, Some(c))
        }
    };
    Ok(Stmt { kind: kind.to_string(), name, binders, hyps, concl, doc })
}

/// The Lean name in a doc comment "... `NAME` ..." after `prefix`.
fn doc_name<'s>(doc: &'s str, prefix: &str) -> Option<&'s str> {
    let r = doc.strip_prefix(prefix)?;
    let r = r.strip_prefix('`')?;
    Some(&r[..r.find('`')?])
}

/// The checked environment: MM0 terms standing for Lean constants and projections.
struct Names {
    /// MM0 term name → Lean name.
    lean: HashMap<String, String>,
    /// MM0 projection term name → Lean structure name.
    proj: HashMap<String, String>,
}

/// A statement giving a constant's type: the MM0 names of its level variables (in the order of
/// the constant's universe parameters), the type, and whether it is proved.
struct TypeClaim<'s> {
    stmt: &'s str,
    levels: Vec<&'s str>,
    ty: &'s M,
    proved: bool,
}

/// The result: declarations checked and the problems found.
pub struct Report {
    pub checked: usize,
    pub problems: Vec<String>,
}

/// Check the statements against the export.
pub fn check(export: &ExportFile<'_>, stmts: &[Stmt]) -> Report {
    let mut names = Names { lean: HashMap::new(), proj: HashMap::new() };
    // Lean name → the statement of the MM0 term standing for it
    let mut by_lean: HashMap<String, &Stmt> = HashMap::new();
    let mut problems = Vec::new();
    for s in stmts {
        if s.kind != "term" && s.kind != "def" {
            continue
        }
        if let Some(n) = doc_name(&s.doc, "Projections of the structure ") {
            names.proj.insert(s.name.clone(), n.to_string());
            continue
        }
        let Some(rest) = s.doc.strip_prefix("Lean ") else { continue };
        let Some(n) = rest.find('`').and_then(|i| doc_name(&rest[i..], "")) else { continue };
        if by_lean.insert(n.to_string(), s).is_some() {
            problems.push(format!("{n}: two MM0 terms claim it"));
        }
        names.lean.insert(s.name.clone(), n.to_string());
    }
    // type statements, by MM0 term
    let mut claims: HashMap<&str, Vec<TypeClaim>> = HashMap::new();
    for s in stmts {
        if s.kind != "axiom" && s.kind != "theorem" {
            continue
        }
        let Some(c) = &s.concl else { continue };
        // the first binder is the context `G`, then come the level variables
        let Some((g, _)) = s.binders.first().filter(|b| b.1 == "ctx") else { continue };
        // nothing else, so no variable can be mistaken for a constant
        if s.binders[1..].iter().any(|b| b.1 != "lvl") {
            continue
        }
        let lvls: Vec<&str> = s.binders[1..].iter().map(|b| b.0.as_str()).collect();
        // `ty G (c us) T` (proved for a definition or theorem), or the `constDF` axiom
        // `leqv u u2 > ... > deq G (c us) (c us2) T`
        let (term, ty) = match (c.head.as_str(), c.args.as_slice()) {
            ("ty", [gv, ce, t]) if gv.head == *g && gv.args.is_empty() => (ce, t),
            ("deq", [gv, ce, _, t]) if gv.head == *g && gv.args.is_empty() && s.kind == "axiom" => (ce, t),
            _ => continue,
        };
        if !names.lean.contains_key(&term.head) {
            continue
        }
        let n = term.args.len();
        if n > lvls.len() || term.args.iter().zip(&lvls).any(|(a, v)| !a.args.is_empty() || a.head != *v) {
            continue
        }
        let proved = s.kind == "theorem" && c.head == "ty" && s.hyps.is_empty();
        claims.entry(term.head.as_str()).or_default().push(TypeClaim { stmt: &s.name, levels: lvls[..n].to_vec(), ty, proved });
    }

    let mut checked = 0;
    let mut seen = std::collections::HashSet::new();
    for d in export.declars.values() {
        export.with_ctx(|ctx| {
            let info = *d.info();
            let lean = lean_name(ctx, info.name);
            seen.insert(lean.clone());
            let Some(&term) = by_lean.get(&lean) else {
                problems.push(format!("{lean}: no MM0 term stands for it"));
                return
            };
            let uparams: Vec<NamePtr> = ctx.read_levels(info.uparams).iter().map(|&l| match ctx.read_level(l) {
                Level::Param(n, _) => n,
                _ => unreachable!("universe parameters are parameters"),
            }).collect();
            let term_lvls: Vec<&str> = term.binders.iter().map(|b| b.0.as_str()).collect();
            if term.binders.iter().any(|b| b.1 != "lvl") || term_lvls.len() != uparams.len() {
                problems.push(format!("{lean}: `{}` does not take its {} universe parameters", term.name, uparams.len()));
                return
            }
            let cs = claims.get(term.name.as_str()).map(Vec::as_slice).unwrap_or_default();
            if cs.is_empty() {
                problems.push(format!("{lean}: no statement gives the type of `{}`", term.name));
            }
            for c in cs {
                let lv = LevelVars::new(&c.levels, &uparams);
                let mut cmp = Cmp { ctx, names: &names, lv: &lv, why: None };
                if !cmp.expr(c.ty, info.ty) {
                    problems.push(format!("{lean}: `{}` states another type ({})", c.stmt, cmp.why.unwrap_or_default()));
                }
            }
            // a theorem's or definition's type is proved, not assumed
            if matches!(d, Declar::Theorem { .. } | Declar::Definition { .. }) && !cs.iter().any(|c| c.proved) {
                problems.push(format!("{lean}: no proved statement of its type"));
            }
            let val = match d {
                Declar::Definition { val, .. } => Some(*val),
                _ => None,
            };
            // a definition's body must be the value (a theorem's is the proof, not stated)
            if let Some(v) = val {
                match &term.concl {
                    Some(body) if term.kind == "def" => {
                        let lv = LevelVars::new(&term_lvls, &uparams);
                        let mut cmp = Cmp { ctx, names: &names, lv: &lv, why: None };
                        if !cmp.expr(body, v) {
                            problems.push(format!("{lean}: the body of `{}` is not its value ({})", term.name, cmp.why.unwrap_or_default()));
                        }
                    }
                    _ => problems.push(format!("{lean}: `{}` is not a definition with a body", term.name)),
                }
            }
            checked += 1;
        });
    }
    for (n, s) in &by_lean {
        if !seen.contains(n) {
            problems.push(format!("`{}` claims to stand for {n}, which the export does not declare", s.name));
        }
    }
    Report { checked, problems }
}

/// Lean's dotted name.
pub(crate) fn lean_name<'t>(ctx: &TcCtx<'t, '_>, n: NamePtr<'t>) -> String {
    match ctx.read_name(n) {
        Name::Anon => String::new(),
        Name::Str(p, s, _) => {
            let p = lean_name(ctx, p);
            let s = ctx.read_string(s).to_string();
            if p.is_empty() { s } else { format!("{p}.{s}") }
        }
        Name::Num(p, k, _) => {
            let p = lean_name(ctx, p);
            if p.is_empty() { k.to_string() } else { format!("{p}.{k}") }
        }
    }
}

/// MM0 level variables and the universe parameters they stand for.
struct LevelVars<'t> {
    map: HashMap<String, NamePtr<'t>>,
}

impl<'t> LevelVars<'t> {
    fn new(mm0: &[&str], lean: &[NamePtr<'t>]) -> Self {
        LevelVars { map: mm0.iter().zip(lean).map(|(m, &l)| (m.to_string(), l)).collect() }
    }
}

/// Comparison of an MM0 expression with a Lean one (the translation, read backwards).
struct Cmp<'a, 't, 'p> {
    ctx: &'a mut TcCtx<'t, 'p>,
    names: &'a Names,
    lv: &'a LevelVars<'t>,
    /// The first place they differ, for the report.
    why: Option<String>,
}

/// What a Lean bound variable refers to, innermost last: a binder (a bound variable on the MM0
/// side too), or a `let` (inlined: its value, which was made in the environment below it). A
/// `Jump` marks where an inlined value is being compared: lookups inside it continue below its
/// `let`, but on the MM0 side the value sits where it is used, so the binders skipped count.
#[derive(Clone, Copy)]
enum Bound<'t> {
    Binder,
    Let(ExprPtr<'t>),
    Jump(usize),
}

impl<'t, 'p> Cmp<'_, 't, 'p> {
    /// Is `m` the translation of the closed expression `e`?
    fn expr(&mut self, m: &M, e: ExprPtr<'t>) -> bool { self.under(m, e, &mut Vec::new()) }

    /// `m` against `e` under `env`. The translation inlines each `let`, so a variable bound by a
    /// `let` is compared as its value, and the MM0 index of one bound by a binder counts only
    /// the binders in between.
    fn under(&mut self, m: &M, e: ExprPtr<'t>, env: &mut Vec<Bound<'t>>) -> bool {
        let x = self.ctx.read_expr(e);
        match (m.head.as_str(), m.args.as_slice(), x) {
            (_, _, Expr::Let { val, body, .. }) => {
                env.push(Bound::Let(val));
                let r = self.under(m, body, env);
                env.pop();
                r
            }
            (_, _, Expr::StringLit { ptr, .. }) => match self.ctx.str_lit_to_constructor(ptr) {
                Some(x) => self.under(m, x, env),
                None => false,
            },
            (_, _, Expr::Var { dbj_idx, .. }) => {
                // find the entry, counting the MM0 binders passed (including skipped ones)
                let (mut p, mut left, mut j) = (env.len(), dbj_idx as usize, 0);
                let target = loop {
                    let Some(q) = p.checked_sub(1) else { return self.fail("a loose bound variable".into()) };
                    match env[q] {
                        Bound::Jump(to) => {
                            j += env[to..q].iter().filter(|b| matches!(b, Bound::Binder)).count();
                            p = to;
                            continue
                        }
                        b if left == 0 => break (q, b),
                        b => {
                            j += usize::from(matches!(b, Bound::Binder));
                            left -= 1;
                            p = q;
                        }
                    }
                };
                match target {
                    (_, Bound::Binder) => {
                        m.head == "bvar" && m.args.len() == 1 && unary(&m.args[0]) == Some(j)
                            || self.fail(format!("MM0 `{}` against bound variable {j}", m.head))
                    }
                    (q, Bound::Let(v)) => {
                        env.push(Bound::Jump(q));
                        let r = self.under(m, v, env);
                        env.pop();
                        r
                    }
                    (_, Bound::Jump(_)) => unreachable!(),
                }
            }
            ("srt", [l], Expr::Sort { level, .. }) => self.level(l, level) || self.fail("a sort's level differs".into()),
            ("app", [f, a], Expr::App { fun, arg, .. }) => self.under(f, fun, env) && self.under(a, arg, env),
            ("lam", [a, b], Expr::Lambda { binder_type, body, .. }) | ("pi", [a, b], Expr::Pi { binder_type, body, .. }) => {
                if !self.under(a, binder_type, env) {
                    return false
                }
                env.push(Bound::Binder);
                let r = self.under(b, body, env);
                env.pop();
                r
            }
            ("lit", [n], Expr::NatLit { ptr, .. }) => binary(n).as_ref() == self.ctx.read_bignum(ptr),
            (h, [i, s], Expr::Proj { ty_name, idx, structure, .. }) if self.names.proj.contains_key(h) => {
                self.names.proj[h] == lean_name(self.ctx, ty_name) && unary(i) == Some(idx) && self.under(s, structure, env)
            }
            (h, ls, Expr::Const { name, levels, .. }) if self.names.lean.contains_key(h) => {
                let levels = self.ctx.read_levels(levels);
                let n = lean_name(self.ctx, name);
                (self.names.lean[h] == n && ls.len() == levels.len() && ls.iter().zip(levels.iter()).all(|(m, &l)| self.level(m, l)))
                    || self.fail(format!("MM0 `{h}` against Lean {n} (or their levels differ)"))
            }
            (h, args, x) => {
                let kind = format!("{x:?}");
                let kind: String = kind.chars().take_while(|c| c.is_alphanumeric()).collect();
                self.fail(format!("MM0 `{h}` with {} arguments against Lean {kind}", args.len()))
            }
        }
    }

    fn fail(&mut self, why: String) -> bool {
        self.why.get_or_insert(why);
        false
    }

    fn level(&mut self, m: &M, l: LevelPtr<'t>) -> bool {
        match (m.head.as_str(), m.args.as_slice(), self.ctx.read_level(l)) {
            ("lz", [], Level::Zero) => true,
            ("ls", [a], Level::Succ(x, _)) => self.level(a, x),
            ("lmax", [a, b], Level::Max(x, y, _)) | ("limax", [a, b], Level::IMax(x, y, _)) => self.level(a, x) && self.level(b, y),
            (v, [], Level::Param(n, _)) => self.lv.map.get(v).is_some_and(|&p| lean_name(self.ctx, p) == lean_name(self.ctx, n)),
            _ => false,
        }
    }
}

/// A unary numeral `z`, `s (s z)`, ...
fn unary(m: &M) -> Option<usize> {
    match (m.head.as_str(), m.args.as_slice()) {
        ("z", []) => Some(0),
        ("s", [a]) => Some(unary(a)? + 1),
        _ => None,
    }
}

/// A binary numeral `b0`, `bd1 (bd0 b0)`, ... (most significant digit innermost).
fn binary(m: &M) -> Option<BigUint> {
    match (m.head.as_str(), m.args.as_slice()) {
        ("b0", []) => Some(BigUint::default()),
        ("bd0", [a]) => Some(binary(a)? << 1u32),
        ("bd1", [a]) => Some((binary(a)? << 1u32) + 1u32),
        _ => None,
    }
}
