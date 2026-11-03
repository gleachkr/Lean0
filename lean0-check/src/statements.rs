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
//! An inductive block certified by the spec's schema (audit §4) has no term per constant: its
//! data definition `def X_D (us): ind = ind_mk X_blk P T` (doc "The inductive block of
//! `X`...") is compared with the export's declaration (the parameters, each type's type and
//! each constructor's type, with the binders' type annotations consumed as the kernel does,
//! and the block's types as variables outside the parameters), and its types, constructors
//! and recursors are the terms `ind_ty (X_D us) i`, `ind_ctor (X_D us) i c` and
//! `ind_rec (X_D us) i v`, named by the export's `all` and constructor lists and `X.rec`.
//!
//! Like the rest of this crate it is independent of the generator: it parses the `.mm0` text
//! itself, for exactly the forms lean0 writes. What it does not check: the generated axioms
//! of blocks left to stage A, quotients and literals (audit §4, §5), and that the certificate
//! proves the statements (the verifiers' job).

use nanoda_lib::env::Declar;
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::name::Name;
use nanoda_lib::util::{ExportFile, ExprPtr, LevelPtr, NamePtr, TcCtx};
use num_bigint::BigUint;
use std::collections::HashMap;

/// An MM0 expression as written: a head and its arguments (a bare identifier has none).
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// From the spec (`spec_statements`), not a certificate: it stands for a Lean declaration
    /// only when the export has it.
    spec: bool,
}

/// The spec's statements between its `-- lean0-check: begin` and `-- lean0-check: end` lines
/// (written in prefix form for this): the data of Lean's `Nat` and `Eq` (`nat_D`, `eq_D`) and
/// the quotient primitives, which the export's declarations are compared with (audit §4).
pub fn spec_statements(spec: &str) -> Result<Vec<Stmt>, String> {
    let (b, e) = ("-- lean0-check: begin", "-- lean0-check: end");
    let Some(i) = spec.find(b) else { return Ok(Vec::new()) };
    let r = &spec[i + b.len()..];
    let Some(j) = r.find(e) else { return Err("spec: `lean0-check: begin` without `end`".into()) };
    let mut out = parse_mm0(&r[..j]).map_err(|e| format!("spec: {e}"))?;
    for s in &mut out {
        s.spec = true;
    }
    Ok(out)
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
    Ok(Stmt { kind: kind.to_string(), name, binders, hyps, concl, doc, spec: false })
}

/// The Lean name in a doc comment "... `NAME` ..." after `prefix`.
fn doc_name<'s>(doc: &'s str, prefix: &str) -> Option<&'s str> {
    let r = doc.strip_prefix(prefix)?;
    let r = r.strip_prefix('`')?;
    Some(&r[..r.find('`')?])
}

/// A stage-B block's data definition, as written.
struct BlockData<'s> {
    stmt: &'s Stmt,
    /// The Lean name of its first type (from the doc).
    lean: String,
    atom: String,
    /// The parameters, outermost first.
    params: Vec<&'s M>,
    /// Each type's type and its constructors' types: the declared types, then the auxiliary
    /// types of a nested block (`ind_mkn`; audit §4).
    types: Vec<(&'s M, Vec<&'s M>)>,
    /// The nested occurrences, one per auxiliary type, written like a constructor type at
    /// depth 0 (`ind_mkn`'s last argument).
    nested: Vec<&'s M>,
    /// The Lean names of its declared types and of each one's constructors (from the export).
    type_names: Vec<String>,
    ctor_names: Vec<Vec<String>>,
}

/// The checked environment: MM0 terms standing for Lean constants and projections.
struct Names<'s> {
    /// MM0 term name → Lean name.
    lean: HashMap<String, String>,
    /// MM0 block atom (`X_blk`, the first argument of `proj`) → block.
    proj: HashMap<String, usize>,
    blocks: Vec<BlockData<'s>>,
    /// Data definition name → block.
    by_def: HashMap<String, usize>,
    /// Recursors of the export that take the motive's level first.
    rec_large: HashMap<String, bool>,
}

impl Names<'_> {
    /// The Lean constant an MM0 application stands for, and its level arguments.
    fn const_of<'m>(&self, m: &'m M) -> Option<(String, Vec<&'m M>)> {
        let block = |d: &'m M| -> Option<(&BlockData, Vec<&'m M>)> {
            let b = *self.by_def.get(&d.head)?;
            Some((&self.blocks[b], d.args.iter().collect()))
        };
        match (m.head.as_str(), m.args.as_slice()) {
            ("ind_ty", [d, i]) => {
                let (b, ls) = block(d)?;
                Some((b.type_names.get(unary(i)?)?.clone(), ls))
            }
            ("ind_ctor", [d, i, c]) => {
                let (b, ls) = block(d)?;
                Some((b.ctor_names.get(unary(i)?)?.get(unary(c)?)?.clone(), ls))
            }
            ("ind_rec", [d, i, v]) => {
                let (b, mut ls) = block(d)?;
                // the recursor of a declared type, or `X.rec_k` of the `k`th auxiliary type
                let i = unary(i)?;
                let n0 = b.type_names.len();
                let n = match b.type_names.get(i) {
                    Some(t) => format!("{t}.rec"),
                    None if i < n0 + b.nested.len() => format!("{}.rec_{}", b.type_names[0], i - n0 + 1),
                    None => return None,
                };
                match self.rec_large.get(&n)? {
                    true => ls.insert(0, v),
                    false if v.head == "lz" && v.args.is_empty() => {}
                    false => return None,
                }
                Some((n, ls))
            }
            (h, ls) => Some((self.lean.get(h)?.clone(), ls.iter().collect())),
        }
    }
}

/// What stands for a Lean declaration: an MM0 term, or a member of a stage-B block.
#[derive(Clone, Copy)]
enum Standing<'s> {
    Term(&'s Stmt),
    Block(usize),
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
    let mut names = Names { lean: HashMap::new(), proj: HashMap::new(), blocks: Vec::new(), by_def: HashMap::new(), rec_large: HashMap::new() };
    // Lean name → what stands for it
    let mut by_lean: HashMap<String, Standing> = HashMap::new();
    let mut problems = Vec::new();
    // the export's declarations by Lean name, its inductive blocks and recursors
    let (by_name, ind_types, ind_ctors, rec_large) = export.with_ctx(|ctx| {
        let mut by_name: HashMap<String, &Declar> = HashMap::new();
        let mut types: HashMap<String, Vec<String>> = HashMap::new();
        let mut ctors: HashMap<String, Vec<String>> = HashMap::new();
        let mut large = HashMap::new();
        for d in export.declars.values() {
            by_name.insert(lean_name(ctx, d.info().name), d);
            match d {
                Declar::Inductive(id) => {
                    let n = lean_name(ctx, id.info.name);
                    types.insert(n.clone(), id.all_ind_names.iter().map(|&t| lean_name(ctx, t)).collect());
                    ctors.insert(n, id.all_ctor_names.iter().map(|&c| lean_name(ctx, c)).collect());
                }
                Declar::Recursor(rd) => {
                    let n = lean_name(ctx, rd.info.name);
                    // its block's first type (the major premise's type is another block's for
                    // the recursor of a nested block's auxiliary type)
                    let Some(ind) = rd.all_inductives.first() else { continue };
                    let Some(Declar::Inductive(id)) = export.declars.get(ind) else { continue };
                    let nl = ctx.read_levels(rd.info.uparams).len();
                    let bl = ctx.read_levels(id.info.uparams).len();
                    large.insert(n, nl == bl + 1);
                }
                _ => {}
            }
        }
        (by_name, types, ctors, large)
    });
    names.rec_large = rec_large;
    for s in stmts {
        if s.kind != "term" && s.kind != "def" {
            continue
        }
        if let Some(n) = doc_name(&s.doc, "The inductive block of ") {
            if s.kind == "term" {
                // the atom; the data definition names the block for `proj`
                continue
            }
            let (Some(body), Some(tn)) = (&s.concl, ind_types.get(n)) else {
                if !s.spec {
                    problems.push(format!("`{}`: not a block the export declares", s.name));
                }
                continue
            };
            let Some(bd) = block_data(s, body, n, tn, &ind_ctors) else {
                problems.push(format!("`{}`: not of the form `ind_mk X_blk P T` or `ind_mkn X_blk P T N`", s.name));
                continue
            };
            let b = names.blocks.len();
            names.proj.insert(bd.atom.clone(), b);
            names.by_def.insert(s.name.clone(), b);
            let mut members: Vec<String> = bd.type_names.clone();
            members.extend(bd.ctor_names.iter().flatten().cloned());
            members.extend(bd.type_names.iter().map(|t| format!("{t}.rec")));
            members.extend((1..=bd.nested.len()).map(|k| format!("{}.rec_{k}", bd.type_names[0])));
            for m in members {
                if by_lean.insert(m.clone(), Standing::Block(b)).is_some() {
                    problems.push(format!("{m}: two MM0 terms claim it"));
                }
            }
            names.blocks.push(bd);
            continue
        }
        let Some(rest) = s.doc.strip_prefix("Lean ") else { continue };
        let Some(n) = rest.find('`').and_then(|i| doc_name(&rest[i..], "")) else { continue };
        if s.spec && !by_name.contains_key(n) {
            continue
        }
        if by_lean.insert(n.to_string(), Standing::Term(s)).is_some() {
            problems.push(format!("{n}: two MM0 terms claim it"));
        }
        names.lean.insert(s.name.clone(), n.to_string());
    }
    // type statements, by Lean name
    let mut claims: HashMap<String, Vec<TypeClaim>> = HashMap::new();
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
        // `ty G (c us) T` (proved for a definition or theorem), or the `constDF` lemma
        // `leqv u u2 > ... > deq G (c us) (c us2) T` (an axiom for an opaque constant, a
        // theorem for a member of a stage-B block)
        let (term, ty) = match (c.head.as_str(), c.args.as_slice()) {
            ("ty", [gv, ce, t]) if gv.head == *g && gv.args.is_empty() => (ce, t),
            ("deq", [gv, ce, _, t]) if gv.head == *g && gv.args.is_empty() => (ce, t),
            _ => continue,
        };
        let Some((lean, cls)) = names.const_of(term) else { continue };
        let n = cls.len();
        if n > lvls.len() || cls.iter().zip(&lvls).any(|(a, v)| !a.args.is_empty() || a.head != *v) {
            continue
        }
        let proved = s.kind == "theorem" && c.head == "ty" && s.hyps.is_empty();
        claims.entry(lean).or_default().push(TypeClaim { stmt: &s.name, levels: lvls[..n].to_vec(), ty, proved });
    }
    // the syntactic axioms about a constant `c` (an opaque, an axiom, a stage-A constant):
    // `axiom c_closed (k: nat) (us): closed k (c us)` and the level congruence
    // `axiom c_eeqv (us us2): leqv u u2 > ... > eeqv (c us) (c us2)`
    for s in stmts {
        if s.kind != "axiom" {
            continue
        }
        let Some(c) = &s.concl else { continue };
        let var = |m: &M, i: usize| m.args.is_empty() && s.binders.get(i).is_some_and(|b| b.0 == m.head);
        let lvls_from = |k: usize| s.binders[k..].iter().all(|b| b.1 == "lvl");
        let ok = match (c.head.as_str(), c.args.as_slice()) {
            ("closed", [k, ce]) if names.lean.contains_key(&ce.head) => {
                let n = ce.args.len();
                s.hyps.is_empty() && s.binders.len() == 1 + n && s.binders[0].1 == "nat" && var(k, 0) && lvls_from(1)
                    && ce.args.iter().enumerate().all(|(i, m)| var(m, 1 + i))
            }
            ("eeqv", [a, b]) if names.lean.contains_key(&a.head) => {
                let n = a.args.len();
                a.head == b.head && b.args.len() == n && s.binders.len() == 2 * n && lvls_from(0)
                    && a.args.iter().enumerate().all(|(i, m)| var(m, i))
                    && b.args.iter().enumerate().all(|(i, m)| var(m, n + i))
                    && s.hyps.len() == n
                    && s.hyps.iter().enumerate().all(|(i, h)| h.head == "leqv" && h.args.len() == 2 && var(&h.args[0], i) && var(&h.args[1], n + i))
            }
            _ => continue,
        };
        if !ok {
            problems.push(format!("`{}`: not of the form `{} ...` for a constant", s.name, c.head));
        }
    }
    // the blocks' data against the export's declarations
    for bd in &names.blocks {
        export.with_ctx(|ctx| {
            let Some(Declar::Inductive(id)) = by_name.get(&bd.lean) else {
                problems.push(format!("`{}`: the export does not declare the inductive type {}", bd.stmt.name, bd.lean));
                return
            };
            let uparams: Vec<NamePtr> = ctx.read_levels(id.info.uparams).iter().map(|&l| match ctx.read_level(l) {
                Level::Param(n, _) => n,
                _ => unreachable!("universe parameters are parameters"),
            }).collect();
            let def_lvls: Vec<&str> = bd.stmt.binders.iter().map(|b| b.0.as_str()).collect();
            if bd.stmt.binders.iter().any(|b| b.1 != "lvl") || def_lvls.len() != uparams.len() {
                problems.push(format!("{}: `{}` does not take its {} universe parameters", bd.lean, bd.stmt.name, uparams.len()));
                return
            }
            if bd.params.len() != id.num_params as usize {
                problems.push(format!("{}: `{}` has {} parameters, the export {}", bd.lean, bd.stmt.name, bd.params.len(), id.num_params));
                return
            }
            let lv = LevelVars::new(&def_lvls, &uparams);
            let selfs: Vec<String> = bd.type_names.clone();
            for (i, tn) in bd.type_names.iter().enumerate() {
                let Some(Declar::Inductive(td)) = by_name.get(tn) else {
                    problems.push(format!("{}: the export does not declare {tn}", bd.lean));
                    continue
                };
                if td.info.uparams != id.info.uparams || td.num_params != id.num_params {
                    problems.push(format!("{tn}: differs from {} in parameters", bd.lean));
                    continue
                }
                let (f, ks) = &bd.types[i];
                let want = strip_pis(ctx, td.info.ty);
                let mut cmp = Cmp { ctx, names: &names, lv: &lv, selfs: Some((&selfs, &uparams)), why: None };
                let m = pis(&bd.params, f);
                if !cmp.expr(&m, want) {
                    problems.push(format!("{tn}: `{}` states another type ({})", bd.stmt.name, cmp.why.unwrap_or_default()));
                }
                for (c, cn) in bd.ctor_names[i].iter().enumerate() {
                    let Some(Declar::Constructor(cd)) = by_name.get(cn) else {
                        problems.push(format!("{}: the export does not declare {cn}", bd.lean));
                        continue
                    };
                    if cd.info.uparams != id.info.uparams || cd.num_params != id.num_params || cd.ctor_idx as usize != c {
                        problems.push(format!("{cn}: differs from {} in parameters or index", bd.lean));
                        continue
                    }
                    let want = strip_pis(ctx, cd.info.ty);
                    let mut cmp = Cmp { ctx, names: &names, lv: &lv, selfs: Some((&selfs, &uparams)), why: None };
                    let np = bd.params.len();
                    let Some(k) = restore(ks[c], 0, np, bd.type_names.len(), &bd.nested) else {
                        problems.push(format!("{cn}: `{}` applies an auxiliary type to other arguments than the parameters", bd.stmt.name));
                        continue
                    };
                    let m = pis(&bd.params, &k);
                    if !cmp.expr(&m, want) {
                        problems.push(format!("{cn}: `{}` states another type ({})", bd.stmt.name, cmp.why.unwrap_or_default()));
                    }
                }
            }
        });
    }

    let mut checked = 0;
    let mut seen = std::collections::HashSet::new();
    for d in export.declars.values() {
        export.with_ctx(|ctx| {
            let info = *d.info();
            let lean = lean_name(ctx, info.name);
            seen.insert(lean.clone());
            let Some(&standing) = by_lean.get(&lean) else {
                problems.push(format!("{lean}: no MM0 term stands for it"));
                return
            };
            let uparams: Vec<NamePtr> = ctx.read_levels(info.uparams).iter().map(|&l| match ctx.read_level(l) {
                Level::Param(n, _) => n,
                _ => unreachable!("universe parameters are parameters"),
            }).collect();
            let term = match standing {
                Standing::Term(t) => Some(t),
                Standing::Block(_) => None,
            };
            let what = match standing {
                Standing::Term(t) => format!("`{}`", t.name),
                Standing::Block(b) => format!("the block `{}`", names.blocks[b].stmt.name),
            };
            if let Some(term) = term {
                let term_lvls: Vec<&str> = term.binders.iter().map(|b| b.0.as_str()).collect();
                if term.binders.iter().any(|b| b.1 != "lvl") || term_lvls.len() != uparams.len() {
                    problems.push(format!("{lean}: `{}` does not take its {} universe parameters", term.name, uparams.len()));
                    return
                }
            }
            let cs = claims.get(&lean).map(Vec::as_slice).unwrap_or_default();
            if cs.is_empty() {
                problems.push(format!("{lean}: no statement gives the type of {what}"));
            }
            for c in cs {
                if c.levels.len() != uparams.len() {
                    problems.push(format!("{lean}: `{}` does not take its {} universe parameters", c.stmt, uparams.len()));
                    continue
                }
                let lv = LevelVars::new(&c.levels, &uparams);
                let mut cmp = Cmp { ctx, names: &names, lv: &lv, selfs: None, why: None };
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
                match term.map(|t| (t, &t.concl)) {
                    Some((term, Some(body))) if term.kind == "def" => {
                        let term_lvls: Vec<&str> = term.binders.iter().map(|b| b.0.as_str()).collect();
                        let lv = LevelVars::new(&term_lvls, &uparams);
                        let mut cmp = Cmp { ctx, names: &names, lv: &lv, selfs: None, why: None };
                        if !cmp.expr(body, v) {
                            problems.push(format!("{lean}: the body of `{}` is not its value ({})", term.name, cmp.why.unwrap_or_default()));
                        }
                    }
                    _ => problems.push(format!("{lean}: {what} is not a definition with a body")),
                }
            }
            checked += 1;
        });
    }
    for (n, s) in &by_lean {
        if !seen.contains(n) {
            let what = match s {
                Standing::Term(t) => t.name.clone(),
                Standing::Block(b) => names.blocks[*b].stmt.name.clone(),
            };
            problems.push(format!("`{what}` claims to stand for {n}, which the export does not declare"));
        }
    }
    Report { checked, problems }
}

/// Read a block's data definition `ind_mk X_blk P T`.
fn block_data<'s>(stmt: &'s Stmt, body: &'s M, lean: &str, type_names: &[String], ctors: &HashMap<String, Vec<String>>) -> Option<BlockData<'s>> {
    let (atom, p, t, n) = match (body.head.as_str(), body.args.as_slice()) {
        ("ind_mk", [atom, p, t]) => (atom, p, t, None),
        ("ind_mkn", [atom, p, t, n]) => (atom, p, t, Some(n)),
        _ => return None,
    };
    if !atom.args.is_empty() {
        return None
    }
    // the context lists the innermost parameter first
    let mut params = ctx_list(p)?;
    params.reverse();
    // the occurrences: the first entry is the first auxiliary type
    let nested = match n {
        Some(n) => ctx_list(n)?,
        None => Vec::new(),
    };
    let mut types = Vec::new();
    let mut t = t;
    loop {
        match (t.head.as_str(), t.args.as_slice()) {
            ("tnil", []) => break,
            ("tcons", [f, cs, rest]) => {
                let mut ks = Vec::new();
                let mut c = cs;
                loop {
                    match (c.head.as_str(), c.args.as_slice()) {
                        ("cnil", []) => break,
                        ("ccons", [k, rest]) => {
                            ks.push(k);
                            c = rest;
                        }
                        _ => return None,
                    }
                }
                types.push((f, ks));
                t = rest;
            }
            _ => return None,
        }
    }
    if types.len() != type_names.len() + nested.len() {
        return None
    }
    let ctor_names: Vec<Vec<String>> = type_names.iter().map(|n| ctors.get(n).cloned().unwrap_or_default()).collect();
    if ctor_names.iter().zip(&types).any(|(ns, (_, ks))| ns.len() != ks.len()) {
        return None
    }
    Some(BlockData { stmt, lean: lean.to_string(), atom: atom.head.clone(), params, types, nested, type_names: type_names.to_vec(), ctor_names })
}

/// The entries of a context term `a1 :: a2 :: ... :: []`, in order.
fn ctx_list(m: &M) -> Option<Vec<&M>> {
    let mut out = Vec::new();
    let mut c = m;
    loop {
        match (c.head.as_str(), c.args.as_slice()) {
            ("nil", []) => return Some(out),
            ("cons", [a, rest]) => {
                out.push(a);
                c = rest;
            }
            _ => return None,
        }
    }
}

/// A numeral.
fn nat_m(n: usize) -> M {
    let mut m = M { head: "z".into(), args: vec![] };
    for _ in 0..n {
        m = M { head: "s".into(), args: vec![m] };
    }
    m
}

/// `m` with its free variables (index at least `depth`) raised by `n`.
fn lift_m(m: &M, n: usize, depth: usize) -> M {
    match (m.head.as_str(), m.args.as_slice()) {
        ("bvar", [k]) => match unary(k) {
            Some(i) if i >= depth => M { head: "bvar".into(), args: vec![nat_m(i + n)] },
            _ => m.clone(),
        },
        ("lam" | "pi", [a, b]) => M { head: m.head.clone(), args: vec![lift_m(a, n, depth), lift_m(b, n, depth + 1)] },
        _ => M { head: m.head.clone(), args: m.args.iter().map(|a| lift_m(a, n, depth)).collect() },
    }
}

/// A nested block's constructor type (at depth `d` under the parameters, `n0` declared types)
/// with its auxiliary types restored: `# (d + np + n0 + k)` applied to the parameters and to
/// `is` becomes the `k`th occurrence lifted to depth `d`, applied to `is` (the kernel's
/// `restoreNested`; audit §4). `None` when an auxiliary type is applied to other arguments
/// than the parameters (then the block is not well formed and the certificate is rejected;
/// the comparison here reports it).
fn restore(m: &M, d: usize, np: usize, n0: usize, nested: &[&M]) -> Option<M> {
    // the spine
    let mut args = Vec::new();
    let mut head = m;
    while let ("app", [f, a]) = (head.head.as_str(), head.args.as_slice()) {
        args.push(a);
        head = f;
    }
    args.reverse();
    let aux = match (head.head.as_str(), head.args.as_slice()) {
        ("bvar", [k]) => unary(k).and_then(|t| t.checked_sub(d + np + n0)),
        _ => None,
    };
    if let Some(k) = aux {
        let x = nested.get(k)?;
        if args.len() < np || (0..np).any(|q| *args[q] != M { head: "bvar".into(), args: vec![nat_m(d + np - 1 - q)] }) {
            return None
        }
        let mut r = lift_m(x, d, 0);
        for a in &args[np..] {
            r = M { head: "app".into(), args: vec![r, restore(a, d, np, n0, nested)?] };
        }
        return Some(r)
    }
    match (m.head.as_str(), m.args.as_slice()) {
        ("app", [f, a]) => Some(M { head: "app".into(), args: vec![restore(f, d, np, n0, nested)?, restore(a, d, np, n0, nested)?] }),
        ("lam" | "pi", [a, b]) => Some(M { head: m.head.clone(), args: vec![restore(a, d, np, n0, nested)?, restore(b, d + 1, np, n0, nested)?] }),
        ("proj", [b, i, x]) => Some(M { head: "proj".into(), args: vec![b.clone(), i.clone(), restore(x, d, np, n0, nested)?] }),
        _ => Some(m.clone()),
    }
}

/// `Π params. body`.
fn pis(params: &[&M], body: &M) -> M {
    let mut m = body.clone();
    for &p in params.iter().rev() {
        m = M { head: "pi".into(), args: vec![p.clone(), m] };
    }
    m
}

/// The kernel's `consumeTypeAnnotations` on the head of `e`.
fn consume_annots<'t>(ctx: &TcCtx<'t, '_>, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
    loop {
        let (f, args) = ctx.unfold_apps(e);
        let Expr::Const { name, .. } = ctx.read_expr(f) else { return e };
        let n = lean_name(ctx, name);
        let strip = matches!((n.as_str(), args.len()), ("outParam" | "semiOutParam", 1) | ("optParam" | "autoParam", 2));
        if !strip {
            return e
        }
        e = args[0];
    }
}

/// The `Π` telescope of `ty` with each binder type's annotations consumed: the declaration as
/// the kernel builds recursors from it, and as a block's data states it.
fn strip_pis<'t>(ctx: &mut TcCtx<'t, '_>, ty: ExprPtr<'t>) -> ExprPtr<'t> {
    match ctx.read_expr(ty) {
        Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
            let bt = consume_annots(ctx, binder_type);
            let b = strip_pis(ctx, body);
            ctx.mk_pi(binder_name, binder_style, bt, b)
        }
        _ => ty,
    }
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
    names: &'a Names<'a>,
    lv: &'a LevelVars<'t>,
    /// Inside a block's data: the block's types, which a variable above the binders stands
    /// for (at the block's universe parameters).
    selfs: Option<(&'a [String], &'a [NamePtr<'t>])>,
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
            ("proj", [b, i, s], Expr::Proj { ty_name, idx, structure, .. }) if b.args.is_empty() && self.names.proj.contains_key(&b.head) => {
                let blk = &self.names.blocks[self.names.proj[&b.head]];
                blk.type_names.contains(&lean_name(self.ctx, ty_name)) && unary(i) == Some(idx) && self.under(s, structure, env)
            }
            ("bvar", [k], Expr::Const { name, levels, .. }) if self.selfs.is_some() => {
                // a block's type, as a variable above the binders of its data
                let (selfs, uparams) = self.selfs.unwrap();
                let binders = env.iter().filter(|b| matches!(b, Bound::Binder)).count();
                let n = lean_name(self.ctx, name);
                let Some(j) = unary(k).and_then(|k| k.checked_sub(binders)) else { return self.fail(format!("MM0 bound variable against Lean {n}")) };
                let levels = self.ctx.read_levels(levels);
                let ok = selfs.get(j) == Some(&n) && levels.len() == uparams.len()
                    && levels.iter().zip(uparams).all(|(&l, &u)| matches!(self.ctx.read_level(l), Level::Param(p, _) if lean_name(self.ctx, p) == lean_name(self.ctx, u)));
                ok || self.fail(format!("MM0 type variable {j} against Lean {n}"))
            }
            (_, _, Expr::Const { name, levels, .. }) if self.names.const_of(m).is_some() => {
                let (mn, ls) = self.names.const_of(m).unwrap();
                let levels = self.ctx.read_levels(levels);
                let n = lean_name(self.ctx, name);
                (mn == n && ls.len() == levels.len() && ls.iter().zip(levels.iter()).all(|(m, &l)| self.level(m, l)))
                    || self.fail(format!("MM0 `{mn}` against Lean {n} (or their levels differ)"))
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
