//! The proofs lean0 carries (audit §5): `lean0/baked/Baked.lean` proves, for Lean's
//! definitions of `Nat.div`, `Nat.mod`, `Nat.gcd` and `Nat.bitwise`, the equations the spec's
//! relations `divmod_eqs`, `gcd_eqs`, `land_eqs`, `lor_eqs` and `xor_eqs` ask proofs of.
//! `baked.ndjson` (`scripts/baked.sh`) has the values of its theorems and lemmas in
//! lean4export's format, with those of the few library lemmas they use that an operation's
//! own definition does not depend on. `term` builds a theorem's proof as an expression over
//! the export being certified: a constant the environment has is itself, any other is
//! replaced by its value here. The elaborator then types it like any proof term, so nothing
//! here is trusted, and an export needs nothing beyond the operations.

use crate::elab::{Elab, R};
use nanoda_lib::expr::BinderStyle;
use nanoda_lib::util::{ExprPtr, LevelPtr, LevelsPtr};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use serde_json::Value;

enum Lv {
    Succ(u64),
    Max(u64, u64),
    IMax(u64, u64),
    Param(u64),
}

enum Ex {
    Var(u16),
    Sort(u64),
    Const(u64, Vec<u64>),
    App(u64, u64),
    Lam(u64, u64),
    Pi(u64, u64),
    Let(u64, u64, u64),
    Proj(u64, usize, u64),
    Nat(BigUint),
}

struct Decl {
    params: Vec<u64>,
    value: u64,
}

struct File {
    /// A name's number to its dotted form.
    names: FxHashMap<u64, String>,
    levels: FxHashMap<u64, Lv>,
    exprs: FxHashMap<u64, Ex>,
    decls: FxHashMap<String, Decl>,
}

fn file() -> &'static File {
    static FILE: std::sync::OnceLock<File> = std::sync::OnceLock::new();
    FILE.get_or_init(|| parse(include_str!("../baked/baked.ndjson")).expect("lean0/baked/baked.ndjson"))
}

fn parse(text: &str) -> Result<File, String> {
    let mut f = File { names: FxHashMap::default(), levels: FxHashMap::default(), exprs: FxHashMap::default(), decls: FxHashMap::default() };
    f.names.insert(0, String::new());
    let num = |v: &Value| v.as_u64().ok_or_else(|| format!("not a number: {v}"));
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let v: Value = serde_json::from_str(line).map_err(|e| e.to_string())?;
        let bad = || format!("unexpected line {line}");
        if let Some(i) = v.get("in") {
            let (pre, last) = match (v.get("str"), v.get("num")) {
                (Some(s), _) => (num(&s["pre"])?, s["str"].as_str().ok_or_else(bad)?.to_string()),
                (_, Some(n)) => (num(&n["pre"])?, num(&n["i"])?.to_string()),
                _ => return Err(bad()),
            };
            let pre = f.names.get(&pre).ok_or_else(bad)?;
            let name = if pre.is_empty() { last } else { format!("{pre}.{last}") };
            f.names.insert(num(i)?, name);
        } else if let Some(i) = v.get("il") {
            let two = |x: &Value| -> Result<(u64, u64), String> { Ok((num(&x[0])?, num(&x[1])?)) };
            let l = if let Some(x) = v.get("succ") {
                Lv::Succ(num(x)?)
            } else if let Some(x) = v.get("max") {
                let (a, b) = two(x)?;
                Lv::Max(a, b)
            } else if let Some(x) = v.get("imax") {
                let (a, b) = two(x)?;
                Lv::IMax(a, b)
            } else if let Some(x) = v.get("param") {
                Lv::Param(num(x)?)
            } else {
                return Err(bad())
            };
            f.levels.insert(num(i)?, l);
        } else if let Some(i) = v.get("ie") {
            let e = if let Some(x) = v.get("bvar") {
                Ex::Var(num(x)? as u16)
            } else if let Some(x) = v.get("sort") {
                Ex::Sort(num(x)?)
            } else if let Some(x) = v.get("const") {
                Ex::Const(num(&x["name"])?, x["us"].as_array().ok_or_else(bad)?.iter().map(num).collect::<Result<_, _>>()?)
            } else if let Some(x) = v.get("app") {
                Ex::App(num(&x["fn"])?, num(&x["arg"])?)
            } else if let Some(x) = v.get("lam") {
                Ex::Lam(num(&x["type"])?, num(&x["body"])?)
            } else if let Some(x) = v.get("forallE") {
                Ex::Pi(num(&x["type"])?, num(&x["body"])?)
            } else if let Some(x) = v.get("letE") {
                Ex::Let(num(&x["type"])?, num(&x["value"])?, num(&x["body"])?)
            } else if let Some(x) = v.get("proj") {
                Ex::Proj(num(&x["typeName"])?, num(&x["idx"])? as usize, num(&x["struct"])?)
            } else if let Some(x) = v.get("natVal") {
                Ex::Nat(x.as_str().and_then(|s| s.parse().ok()).ok_or_else(bad)?)
            } else {
                return Err(bad())
            };
            f.exprs.insert(num(i)?, e);
        } else if let Some(d) = v.get("decl") {
            let name = f.names.get(&num(&d["name"])?).ok_or_else(bad)?.clone();
            let params = d["levelParams"].as_array().ok_or_else(bad)?.iter().map(num).collect::<Result<_, _>>()?;
            f.decls.insert(name, Decl { params, value: num(&d["value"])? });
        } else {
            return Err(bad())
        }
    }
    Ok(f)
}

/// Builds the file's expressions over one type checker's context.
pub struct Baked<'t> {
    exprs: FxHashMap<u64, ExprPtr<'t>>,
    levels: FxHashMap<u64, LevelPtr<'t>>,
    /// An inlined declaration's level parameters and value.
    values: FxHashMap<&'static str, (LevelsPtr<'t>, ExprPtr<'t>)>,
}

impl<'t> Default for Baked<'t> {
    fn default() -> Self { Baked { exprs: FxHashMap::default(), levels: FxHashMap::default(), values: FxHashMap::default() } }
}

impl<'t> Baked<'t> {
    /// The proof of the theorem `Lean0.{name}` of `Baked.lean`, as a closed expression over
    /// the environment's constants.
    pub fn term(&mut self, el: &mut Elab<'_, '_, 't, '_>, name: &str) -> R<ExprPtr<'t>> {
        let f = file();
        let Some((key, d)) = f.decls.get_key_value(&format!("Lean0.{name}")) else { return Err(format!("internal: no proof `{name}` is carried")) };
        if !d.params.is_empty() {
            return Err(format!("internal: the proof `{name}` has level parameters"))
        }
        Ok(self.value(el, key)?.1)
    }

    fn value(&mut self, el: &mut Elab<'_, '_, 't, '_>, name: &'static str) -> R<(LevelsPtr<'t>, ExprPtr<'t>)> {
        if let Some(&v) = self.values.get(name) {
            return Ok(v)
        }
        let d = &file().decls[name];
        let mut ks = Vec::new();
        for &p in &d.params {
            let n = el.tc.ctx.str1_owned(file().names[&p].clone());
            ks.push(el.tc.ctx.param(n));
        }
        let ks = el.tc.ctx.alloc_levels_slice(&ks);
        let v = (ks, self.expr(el, d.value)?);
        self.values.insert(name, v);
        Ok(v)
    }

    fn level(&mut self, el: &mut Elab<'_, '_, 't, '_>, l: u64) -> R<LevelPtr<'t>> {
        if l == 0 {
            return Ok(el.tc.ctx.zero())
        }
        if let Some(&p) = self.levels.get(&l) {
            return Ok(p)
        }
        let p = match file().levels.get(&l).ok_or("internal: a level of the carried proofs is missing")? {
            &Lv::Succ(a) => {
                let a = self.level(el, a)?;
                el.tc.ctx.succ(a)
            }
            &Lv::Max(a, b) => {
                let (a, b) = (self.level(el, a)?, self.level(el, b)?);
                el.tc.ctx.max(a, b)
            }
            &Lv::IMax(a, b) => {
                let (a, b) = (self.level(el, a)?, self.level(el, b)?);
                el.tc.ctx.imax(a, b)
            }
            Lv::Param(n) => {
                let n = el.tc.ctx.str1_owned(file().names[n].clone());
                el.tc.ctx.param(n)
            }
        };
        self.levels.insert(l, p);
        Ok(p)
    }

    fn expr(&mut self, el: &mut Elab<'_, '_, 't, '_>, e: u64) -> R<ExprPtr<'t>> {
        if let Some(&p) = self.exprs.get(&e) {
            return Ok(p)
        }
        let f = file();
        let x = el.tc.ctx.str1("x");
        let p = match f.exprs.get(&e).ok_or("internal: an expression of the carried proofs is missing")? {
            &Ex::Var(i) => el.tc.ctx.mk_var(i),
            &Ex::Sort(l) => {
                let l = self.level(el, l)?;
                el.tc.ctx.mk_sort(l)
            }
            Ex::Const(n, us) => {
                let mut ls = Vec::new();
                for &u in us {
                    ls.push(self.level(el, u)?);
                }
                let ls = el.tc.ctx.alloc_levels_slice(&ls);
                let name = &f.names[n];
                // the environment's constant where it has one (declared before this point);
                // the lemmas of `Baked.lean` are never the environment's
                let own = name.starts_with("Lean0.");
                let declared = if own { None } else { el.tc.ctx.export_file.find_name(name).filter(|n| el.tc.env.get_declar(n).is_some()) };
                match (declared, f.decls.get_key_value(name)) {
                    (Some(n), _) => el.tc.ctx.mk_const(n, ls),
                    (None, Some((key, _))) => {
                        let (ks, v) = self.value(el, key)?;
                        el.tc.ctx.subst_expr_levels(v, ks, ls)
                    }
                    (None, None) => return Err(format!("the export lacks `{name}`")),
                }
            }
            &Ex::App(a, b) => {
                let (a, b) = (self.expr(el, a)?, self.expr(el, b)?);
                el.tc.ctx.mk_app(a, b)
            }
            &Ex::Lam(t, b) => {
                let (t, b) = (self.expr(el, t)?, self.expr(el, b)?);
                el.tc.ctx.mk_lambda(x, BinderStyle::Default, t, b)
            }
            &Ex::Pi(t, b) => {
                let (t, b) = (self.expr(el, t)?, self.expr(el, b)?);
                el.tc.ctx.mk_pi(x, BinderStyle::Default, t, b)
            }
            &Ex::Let(t, v, b) => {
                let (t, v, b) = (self.expr(el, t)?, self.expr(el, v)?, self.expr(el, b)?);
                el.tc.ctx.mk_let(x, t, v, b, false)
            }
            &Ex::Proj(n, i, s) => {
                let name = &f.names[&n];
                let Some(n) = el.tc.ctx.export_file.find_name(name) else { return Err(format!("the export lacks `{name}`")) };
                let s = self.expr(el, s)?;
                el.tc.ctx.mk_proj(n, i, s)
            }
            Ex::Nat(k) => el.tc.ctx.mk_nat_lit_quick(k.clone()).ok_or("the export has no Nat literals")?,
        };
        self.exprs.insert(e, p);
        Ok(p)
    }
}
