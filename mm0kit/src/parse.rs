//! A parser for the subset of MM0 that `spec/lean.mm0` uses: sorts, terms, defs, axioms and
//! theorems (no bound variables, no dependencies), with delimiters and notations (`prefix`,
//! `infixl`, `infixr`, `notation`; no coercions), parsed as `mm0.md` specifies.

use crate::bail;
use crate::env::*;
use std::collections::HashMap;

/// A precedence: a number, or `max` (above every number).
type Prec = u32;
const MAX: Prec = Prec::MAX;

/// What follows the leading constant of a `prefix` or `notation`.
#[derive(Clone)]
enum Lit {
    Const(String),
    /// the term's argument with this index, parsed at this precedence
    Var(usize, Prec),
}

/// A notation led by a constant: `prefix`, or `notation`.
#[derive(Clone)]
struct Notation {
    term: TId,
    prec: Prec,
    lits: Vec<Lit>,
}

#[derive(Clone, Copy)]
struct Infix {
    term: TId,
    prec: Prec,
    right: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Punct(char),
    Math(String),
}

struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    /// The text of the last `--|` doc comment block seen.
    doc: Option<String>,
}

impl<'a> Lexer<'a> {
    fn skip_ws(&mut self) {
        let mut doc_lines: Vec<String> = Vec::new();
        loop {
            while self.pos < self.src.len() && self.src[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            if self.src[self.pos..].starts_with(b"--") {
                let start = self.pos;
                while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                    self.pos += 1;
                }
                let line = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
                if let Some(d) = line.strip_prefix("--|") {
                    doc_lines.push(d.strip_prefix(' ').unwrap_or(d).to_string());
                } else {
                    doc_lines.clear();
                }
            } else {
                break
            }
        }
        self.doc = if doc_lines.is_empty() { None } else { Some(doc_lines.join("\n")) };
    }

    fn next(&mut self) -> Result<Option<Tok>> {
        self.skip_ws();
        let Some(&c) = self.src.get(self.pos) else { return Ok(None) };
        if c == b'$' {
            let start = self.pos + 1;
            let Some(len) = self.src[start..].iter().position(|&b| b == b'$') else { bail!("unterminated math string") };
            self.pos = start + len + 1;
            return Ok(Some(Tok::Math(String::from_utf8(self.src[start..start + len].to_vec()).unwrap())))
        }
        if c.is_ascii_alphanumeric() || c == b'_' {
            let start = self.pos;
            while self.pos < self.src.len() && (self.src[self.pos].is_ascii_alphanumeric() || self.src[self.pos] == b'_') {
                self.pos += 1;
            }
            return Ok(Some(Tok::Ident(String::from_utf8(self.src[start..self.pos].to_vec()).unwrap())))
        }
        self.pos += 1;
        Ok(Some(Tok::Punct(c as char)))
    }
}

struct Parser<'a, 'e> {
    lx: Lexer<'a>,
    peeked: Option<Tok>,
    env: &'e mut Env,
    /// delimiters besides `(` and `)` (single characters)
    delims: Vec<char>,
    /// notations by their leading constant
    leading: HashMap<String, Notation>,
    infixes: HashMap<String, Infix>,
}

impl Parser<'_, '_> {
    fn peek(&mut self) -> Result<Option<&Tok>> {
        if self.peeked.is_none() {
            self.peeked = self.lx.next()?;
        }
        Ok(self.peeked.as_ref())
    }

    fn bump(&mut self) -> Result<Option<Tok>> {
        self.peek()?;
        Ok(self.peeked.take())
    }

    fn ident(&mut self) -> Result<String> {
        match self.bump()? {
            Some(Tok::Ident(s)) => Ok(s),
            t => bail!("expected identifier, got {t:?}"),
        }
    }

    fn punct(&mut self, c: char) -> Result<()> {
        match self.bump()? {
            Some(Tok::Punct(d)) if d == c => Ok(()),
            t => bail!("expected '{c}', got {t:?}"),
        }
    }

    fn math(&mut self) -> Result<String> {
        match self.bump()? {
            Some(Tok::Math(m)) => Ok(m.trim().to_string()),
            t => bail!("expected a math string, got {t:?}"),
        }
    }

    /// A precedence: a number or `max`.
    fn prec(&mut self) -> Result<Prec> {
        let p = self.ident()?;
        if p == "max" {
            return Ok(MAX)
        }
        p.parse().map_err(|_| Mm0Error(format!("bad precedence {p}")))
    }

    fn term_id(&self, name: &str) -> Result<(TId, usize)> {
        let Some(&t) = self.env.term_names.get(name) else { bail!("notation for unknown term {name}") };
        Ok((t, self.env.terms[t.0 as usize].args.len()))
    }

    fn sort(&mut self) -> Result<u8> {
        let s = self.ident()?;
        self.env.sort_names.get(&s).copied().ok_or_else(|| Mm0Error(format!("unknown sort {s}")))
    }

    fn binders(&mut self) -> Result<Vec<(String, u8)>> {
        let mut out = Vec::new();
        while let Some(Tok::Punct('(')) = self.peek()? {
            self.bump()?;
            let mut names = Vec::new();
            while let Some(Tok::Ident(_)) = self.peek()? {
                names.push(self.ident()?);
            }
            self.punct(':')?;
            let s = self.sort()?;
            self.punct(')')?;
            out.extend(names.into_iter().map(|n| (n, s)));
        }
        Ok(out)
    }

    fn stmt(&mut self) -> Result<bool> {
        self.peek()?;
        let doc = self.lx.doc.take();
        let Some(tok) = self.bump()? else { return Ok(false) };
        let Tok::Ident(kw) = tok else { bail!("expected a statement, got {tok:?}") };
        let mut mods = 0;
        let mut kw = kw;
        loop {
            match kw.as_str() {
                "pure" => mods |= SORT_PURE,
                "strict" => mods |= SORT_STRICT,
                "provable" => mods |= SORT_PROVABLE,
                "free" => mods |= SORT_FREE,
                _ => break,
            }
            kw = self.ident()?;
        }
        match kw.as_str() {
            "delimiter" => {
                while let Some(Tok::Math(_)) = self.peek()? {
                    for d in self.math()?.split_whitespace() {
                        let mut cs = d.chars();
                        let (Some(c), None) = (cs.next(), cs.next()) else { bail!("only single-character delimiters are supported: {d}") };
                        if c != '(' && c != ')' {
                            self.delims.push(c);
                        }
                    }
                }
                self.punct(';')?;
            }
            "prefix" | "infixl" | "infixr" => {
                let name = self.ident()?;
                self.punct(':')?;
                let tok = self.math()?;
                if self.ident()? != "prec" {
                    bail!("expected `prec` in the notation for {name}")
                }
                let prec = self.prec()?;
                self.punct(';')?;
                let (term, n) = self.term_id(&name)?;
                if kw == "prefix" {
                    // the last argument at the notation's precedence, the others at max
                    let lits = (0..n).map(|i| Lit::Var(i, if i + 1 == n { prec } else { MAX })).collect();
                    self.leading.insert(tok, Notation { term, prec, lits });
                } else {
                    if n != 2 || prec == MAX {
                        bail!("infix notation for {name}: needs two arguments and a precedence below max")
                    }
                    self.infixes.insert(tok, Infix { term, prec, right: kw == "infixr" });
                }
            }
            "notation" => {
                let name = self.ident()?;
                let binders = self.binders()?;
                self.punct(':')?;
                self.sort()?;
                self.punct('=')?;
                // `(c: p)` constants and binder names, the first a constant
                let mut items: Vec<(Option<String>, Prec, Option<usize>)> = Vec::new();
                loop {
                    match self.bump()? {
                        Some(Tok::Punct('(')) => {
                            let c = self.math()?;
                            self.punct(':')?;
                            let p = self.prec()?;
                            self.punct(')')?;
                            items.push((Some(c), p, None));
                        }
                        Some(Tok::Ident(v)) => {
                            let Some(i) = binders.iter().position(|b| b.0 == v) else { bail!("notation for {name}: unknown variable {v}") };
                            items.push((None, 0, Some(i)));
                        }
                        Some(Tok::Punct(';')) => break,
                        t => bail!("notation for {name}: unexpected {t:?}"),
                    }
                }
                let (term, n) = self.term_id(&name)?;
                if binders.len() != n {
                    bail!("notation for {name}: {} variables for {n} arguments", binders.len())
                }
                let Some((Some(lead), prec, _)) = items.first().cloned() else { bail!("notation for {name} must start with a constant") };
                // a variable is parsed one above the constant after it (which must be below
                // max), at max before another variable, and at the notation's precedence at the
                // end (mm0.md, `P`)
                let mut lits = Vec::new();
                for j in 1..items.len() {
                    lits.push(match &items[j] {
                        (Some(c), _, _) => Lit::Const(c.clone()),
                        (None, _, Some(i)) => Lit::Var(*i, match items.get(j + 1) {
                            Some((Some(_), MAX, _)) => bail!("notation for {name}: a constant after a variable needs a precedence below max"),
                            Some((Some(_), p, _)) => p + 1,
                            Some((None, _, _)) => MAX,
                            None => prec,
                        }),
                        (None, _, None) => unreachable!(),
                    });
                }
                let mut vars: Vec<usize> = lits.iter().filter_map(|l| match l { Lit::Var(i, _) => Some(*i), _ => None }).collect();
                vars.sort();
                if vars != (0..n).collect::<Vec<_>>() {
                    bail!("notation for {name} must use each variable once")
                }
                self.leading.insert(lead, Notation { term, prec, lits });
            }
            "sort" => {
                let name = self.ident()?;
                self.punct(';')?;
                self.env.add_sort(&name, mods)?;
            }
            "term" => {
                let name = self.ident()?;
                let mut args = self.binders()?;
                self.punct(':')?;
                let mut ret = self.sort()?;
                while let Some(Tok::Punct('>')) = self.peek()? {
                    self.bump()?;
                    args.push(("_".into(), ret));
                    ret = self.sort()?;
                }
                self.punct(';')?;
                self.env.add_term(TermDecl { name, args, ret, kind: TermKind::Term, local: false, doc })?;
            }
            "def" => {
                let name = self.ident()?;
                let args = self.binders()?;
                self.punct(':')?;
                let ret = self.sort()?;
                let body = match self.bump()? {
                    Some(Tok::Punct('=')) => {
                        let Some(Tok::Math(m)) = self.bump()? else { bail!("expected a formula") };
                        self.punct(';')?;
                        Some(self.formula(&m, &args)?)
                    }
                    Some(Tok::Punct(';')) => None,
                    t => bail!("expected '=' or ';', got {t:?}"),
                };
                let Some(body) = body else { bail!("def {name} without a body is not supported in a spec") };
                self.env.add_term(TermDecl { name, args, ret, kind: TermKind::Def { body, public_body: true }, local: false, doc })?;
            }
            "axiom" | "theorem" => {
                let axiom = kw == "axiom";
                let name = self.ident()?;
                let args = self.binders()?;
                self.punct(':')?;
                let mut fs = Vec::new();
                loop {
                    let Some(Tok::Math(m)) = self.bump()? else { bail!("expected a formula in {name}") };
                    fs.push(self.formula(&m, &args)?);
                    match self.bump()? {
                        Some(Tok::Punct('>')) => {}
                        Some(Tok::Punct(';')) => break,
                        t => bail!("expected '>' or ';', got {t:?}"),
                    }
                }
                let concl = fs.pop().unwrap();
                if !axiom {
                    bail!("theorem {name}: theorems in a spec need proofs, which this parser cannot read")
                }
                self.env.add_thm(ThmDecl { name: name.into(), args: args.into(), hyps: fs.into(), concl, axiom, local: false, proof: None, doc: doc.map(Into::into) })?;
            }
            k => bail!("unsupported statement {k}"),
        }
        Ok(true)
    }

    fn formula(&mut self, m: &str, vars: &[(String, u8)]) -> Result<E> {
        // split on whitespace, and around delimiters
        let mut toks: Vec<String> = Vec::new();
        for word in m.split_whitespace() {
            let mut cur = String::new();
            for c in word.chars() {
                if c == '(' || c == ')' || self.delims.contains(&c) {
                    if !cur.is_empty() {
                        toks.push(std::mem::take(&mut cur));
                    }
                    toks.push(c.to_string());
                } else {
                    cur.push(c);
                }
            }
            if !cur.is_empty() {
                toks.push(cur);
            }
        }
        let mut pos = 0;
        let e = self.expr(&toks, &mut pos, vars, 0)?;
        if pos != toks.len() {
            bail!("trailing tokens in formula: {m}")
        }
        Ok(e)
    }

    /// `expression(p)` of `mm0.md`, by precedence climbing over the infix operators.
    fn expr(&mut self, toks: &[String], pos: &mut usize, vars: &[(String, u8)], p: Prec) -> Result<E> {
        let mut lhs = self.prefix_expr(toks, pos, vars, p)?;
        while let Some(&op) = toks.get(*pos).and_then(|t| self.infixes.get(t)) {
            if op.prec < p {
                break
            }
            *pos += 1;
            let rhs = self.expr(toks, pos, vars, if op.right { op.prec } else { op.prec + 1 })?;
            lhs = self.env.app(op.term, &[lhs, rhs]);
        }
        Ok(lhs)
    }

    /// A parenthesized expression, a variable, a notation led by a constant (at its precedence)
    /// or a term applied to its arguments (at precedence 1024).
    fn prefix_expr(&mut self, toks: &[String], pos: &mut usize, vars: &[(String, u8)], p: Prec) -> Result<E> {
        let Some(t) = toks.get(*pos) else { bail!("unexpected end of formula") };
        *pos += 1;
        if t == "(" {
            let e = self.expr(toks, pos, vars, 0)?;
            if toks.get(*pos).map(String::as_str) != Some(")") {
                bail!("expected ')'")
            }
            *pos += 1;
            return Ok(e)
        }
        if let Some(i) = vars.iter().position(|v| v.0 == *t) {
            return Ok(self.env.var(i as u16))
        }
        if let Some(n) = self.leading.get(t).cloned() {
            if n.prec < p {
                bail!("`{t}` needs parentheses here")
            }
            let mut args = vec![None; n.lits.iter().filter(|l| matches!(l, Lit::Var(..))).count()];
            for lit in &n.lits {
                match lit {
                    Lit::Const(c) => {
                        if toks.get(*pos) != Some(c) {
                            bail!("expected `{c}` in the notation `{t}`")
                        }
                        *pos += 1;
                    }
                    Lit::Var(i, q) => args[*i] = Some(self.expr(toks, pos, vars, *q)?),
                }
            }
            let args: Vec<E> = args.into_iter().map(|a| a.expect("every argument has a place")).collect();
            return Ok(self.env.app(n.term, &args))
        }
        let Some(&tid) = self.env.term_names.get(t) else { bail!("unknown identifier {t}") };
        let n = self.env.terms[tid.0 as usize].args.len();
        if n > 0 && p > 1024 {
            bail!("application of {t} needs parentheses")
        }
        let mut args = Vec::with_capacity(n);
        for _ in 0..n {
            args.push(self.expr(toks, pos, vars, MAX)?);
        }
        Ok(self.env.app(tid, &args))
    }
}

/// Parse an `.mm0` file in the supported subset, adding its statements to `env`.
pub fn parse_into(env: &mut Env, src: &str) -> Result<()> {
    let mut p = Parser {
        lx: Lexer { src: src.as_bytes(), pos: 0, doc: None },
        peeked: None,
        env,
        delims: Vec::new(),
        leading: HashMap::new(),
        infixes: HashMap::new(),
    };
    while p.stmt()? {}
    Ok(())
}
