//! The division-like literal operations (audit §5): `Nat.div`, `Nat.mod`, `Nat.gcd`,
//! `Nat.land`, `Nat.lor` and `Nat.xor`. Lean defines them by fuel and well-founded
//! recursion; the spec's relations `divmod_eqs`, `gcd_eqs`, `land_eqs`, `lor_eqs` and
//! `xor_eqs` ask instead for proofs, in the theory, of equations that determine each function
//! (`y * (x / y) + x % y = x`, `0 < y → x % y < y`, ...). This module gives those proofs
//! for the environment's definitions: the proof terms lean0 carries (`baked`), elaborated
//! like any other, and states the relation as the theorem `{cname}_eqs` (`eqs_theorem`);
//! `natlit::op_axioms` then proves the `_lit` theorems from the spec's rules.

use crate::baked::Baked;
use crate::elab::{mm, Elab, R};
use crate::gen::add_thm;
use mm0kit::env::{ThId, E, P};
use nanoda_lib::expr::BinderStyle;
use nanoda_lib::util::{ExprPtr, LevelPtr};
use num_bigint::BigUint;

/// An operation with a relation in the spec, and the pair of division and modulus its
/// relation is about.
pub struct Op {
    pub lean: &'static str,
    pub rel: &'static str,
    pair: Pair,
}

/// The functions `fd fm` of a `divmod_eqs`. Lean's `Nat.div` does not depend on `Nat.mod`,
/// nor `Nat.mod` and `Nat.gcd` on `Nat.div`, so the one an operation's definition lacks is a
/// term lean0 carries, a copy of Lean's definition (`Baked.lean`: an export needs only the
/// operation). The multiplication is always such a term, the addition is `Nat.add`.
#[derive(Clone, Copy, PartialEq)]
enum Pair {
    /// `Nat.div` and the copy of `Nat.mod`.
    Div,
    /// The copy of `Nat.div` and `Nat.mod`.
    Mod,
    /// `Nat.div` and `Nat.mod`.
    Both,
}

impl Pair {
    /// The key of the pair's `divmod_eqs` theorem in `Gen::nat_eqs`.
    fn key(self) -> &'static str {
        match self {
            Pair::Div => "Nat.div",
            Pair::Mod => "Nat.mod",
            Pair::Both => "Nat.div, Nat.mod",
        }
    }

    /// The carried proofs of `y * (x / y) + x % y = x`, `0 < y → x % y < y`, `x / 0 = 0`.
    fn proofs(self) -> [&'static str; 3] {
        match self {
            Pair::Div => ["d_div_add_mod", "c_mod_lt", "d_div_zero"],
            Pair::Mod => ["m_div_add_mod", "mod_lt", "c_div_zero"],
            Pair::Both => ["div_add_mod", "mod_lt", "d_div_zero"],
        }
    }
}

pub const OPS: &[Op] = &[
    Op { lean: "Nat.div", rel: "divmod_eqs", pair: Pair::Div },
    Op { lean: "Nat.mod", rel: "divmod_eqs", pair: Pair::Mod },
    Op { lean: "Nat.gcd", rel: "gcd_eqs", pair: Pair::Mod },
    Op { lean: "Nat.land", rel: "land_eqs", pair: Pair::Both },
    Op { lean: "Nat.lor", rel: "lor_eqs", pair: Pair::Both },
    Op { lean: "Nat.xor", rel: "xor_eqs", pair: Pair::Both },
];

pub fn op(lean: &str) -> Option<&'static Op> { OPS.iter().find(|o| o.lean == lean) }

/// The types the relations' premises are stated with: Lean's `Eq` and `Nat.le` must be the
/// spec's blocks (`eq_D`, `le_D`).
const BLOCKS: &[(&str, &str)] = &[("Eq", "eq_D"), ("Nat.le", "le_D")];

type Ex<'t> = ExprPtr<'t>;
type El<'a, 'x, 't, 'p> = Elab<'a, 'x, 't, 'p>;

// ------------------------------------------------------------------ terms

fn konst<'t>(el: &mut El<'_, '_, 't, '_>, s: &str, ls: &[LevelPtr<'t>]) -> R<Ex<'t>> {
    let n = el.tc.ctx.export_file.find_name(s).ok_or_else(|| format!("no `{s}`"))?;
    let ls = el.tc.ctx.alloc_levels_slice(ls);
    Ok(el.tc.ctx.mk_const(n, ls))
}

fn app<'t>(el: &mut El<'_, '_, 't, '_>, f: Ex<'t>, args: &[Ex<'t>]) -> Ex<'t> {
    args.iter().fold(f, |f, &a| el.tc.ctx.mk_app(f, a))
}

fn pi<'t>(el: &mut El<'_, '_, 't, '_>, x: &'static str, ty: Ex<'t>, body: Ex<'t>) -> Ex<'t> {
    let n = el.tc.ctx.str1(x);
    el.tc.ctx.mk_pi(n, BinderStyle::Default, ty, body)
}

/// The terms the premises are built from.
struct Voc<'t> {
    nat: Ex<'t>,
    succ: Ex<'t>,
    /// `@Eq.{1} Nat`, `Nat.le`.
    eq: Ex<'t>,
    le: Ex<'t>,
    /// The pair's division and modulus, the carried multiplication, `Nat.add`.
    div: Ex<'t>,
    mod_: Ex<'t>,
    mul: Ex<'t>,
    add: Ex<'t>,
    lits: [Ex<'t>; 3],
}

impl<'t> Voc<'t> {
    fn new(el: &mut El<'_, '_, 't, '_>, b: &mut Baked<'t>, pair: Pair) -> R<Self> {
        let nat = konst(el, "Nat", &[])?;
        let one = {
            let z = el.tc.ctx.zero();
            el.tc.ctx.succ(z)
        };
        let eq = konst(el, "Eq", &[one])?;
        let eq = app(el, eq, &[nat]);
        let mut lits = [nat; 3];
        for (i, l) in lits.iter_mut().enumerate() {
            *l = el.tc.ctx.mk_nat_lit_quick(BigUint::from(i)).ok_or("the export has no Nat literals")?;
        }
        Ok(Voc {
            nat,
            succ: konst(el, "Nat.succ", &[])?,
            eq,
            le: konst(el, "Nat.le", &[])?,
            div: if pair == Pair::Mod { b.term(el, "div")? } else { konst(el, "Nat.div", &[])? },
            mod_: if pair == Pair::Div { b.term(el, "mod")? } else { konst(el, "Nat.mod", &[])? },
            mul: b.term(el, "mul")?,
            add: konst(el, "Nat.add", &[])?,
            lits,
        })
    }

    /// `Π x y : Nat. body`, with `body` at depth 2 (`y` is `#0`, `x` is `#1`).
    fn pi2(&self, el: &mut El<'_, '_, 't, '_>, body: Ex<'t>) -> Ex<'t> {
        let inner = pi(el, "y", self.nat, body);
        pi(el, "x", self.nat, inner)
    }

    fn eq(&self, el: &mut El<'_, '_, 't, '_>, a: Ex<'t>, b: Ex<'t>) -> Ex<'t> { app(el, self.eq, &[a, b]) }

    /// `a < b`, as `Nat.le (succ a) b`.
    fn lt(&self, el: &mut El<'_, '_, 't, '_>, a: Ex<'t>, b: Ex<'t>) -> Ex<'t> {
        let sa = app(el, self.succ, &[a]);
        app(el, self.le, &[sa, b])
    }

    /// The arguments `fd fm fmul fadd` of the relations.
    fn divmod_args(&self, el: &mut El<'_, '_, 't, '_>) -> R<Vec<E>> { [self.div, self.mod_, self.mul, self.add].iter().map(|&e| el.tr(e)).collect() }
}

/// `closed nz e`.
fn closed<'t>(el: &mut El<'_, '_, 't, '_>, e: Ex<'t>) -> R<P> {
    let m = el.tr(e)?;
    let g = &mut *el.g;
    let zk = g.lean.nat(&mut g.env, 0);
    mm(g.lean.closed(&mut g.env, zk, m))
}

/// The `_eqs` theorem of `lean`, at `G`.
fn fact(el: &mut El<'_, '_, '_, '_>, lean: &str) -> R<P> {
    let Some(&th) = el.g.nat_eqs.get(lean) else { return Err(format!("the equations of `{lean}` were not derived")) };
    let gv = el.g.env.var(0);
    mm(el.g.env.thm(th, &[gv], &[]))
}

/// `⟦ₜ G ⊢ c : T ⟧` for the constant `lean`, from its typing lemma.
fn typing(el: &mut El<'_, '_, '_, '_>, lean: &str) -> R<P> {
    let th = el.g.consts[lean].ty_thm;
    let gv = el.g.env.var(0);
    mm(el.g.env.thm(th, &[gv], &[]))
}

/// `⟦ₜ G ⊢ e : Nat → Nat → Nat ⟧` for a closed term.
fn binop<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, e: Ex<'t>) -> R<P> {
    let (t, p) = el.infer(e)?;
    let ty = v.pi2(el, v.nat);
    el.cast(p, t, ty)
}

/// A defining equation `lhs ≡ rhs` over `n` fresh variables of type `Nat` (the first is the
/// outer one).
fn eqn<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, n: usize, f: impl FnOnce(&mut El<'_, '_, 't, '_>, &[Ex<'t>]) -> (Ex<'t>, Ex<'t>)) -> R<P> {
    let mut xs = Vec::new();
    let mut r = Ok(());
    for x in ["x", "y"].into_iter().take(n) {
        let name = el.tc.ctx.str1(x);
        match el.open_pub(name, BinderStyle::Default, v.nat) {
            Ok(x) => xs.push(x),
            Err(e) => {
                r = Err(e);
                break
            }
        }
    }
    let p = r.and_then(|()| {
        let (lhs, rhs) = f(el, &xs);
        let p = el.defeq(lhs, rhs)?;
        // at `Nat`: the type of a recursor's application is its motive's
        let from = el.infer(lhs)?.0;
        el.cast(p, from, v.nat)
    });
    for _ in 0..xs.len() {
        el.close_pub();
    }
    p
}

/// `mul_eqs G mul Nat.add` for the carried multiplication (recursion on the second
/// argument with `Nat.add`): its two equations hold by unfolding.
fn mul_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>) -> R<P> {
    let zero = konst(el, "Nat.zero", &[])?;
    let mut hyps = vec![fact(el, "Nat.add")?, closed(el, v.mul)?, binop(el, v, v.mul)?];
    hyps.push(eqn(el, v, 1, |el, xs| (app(el, v.mul, &[xs[0], zero]), zero))?);
    hyps.push(eqn(el, v, 2, |el, xs| {
        let sy = app(el, v.succ, &[xs[1]]);
        let r = app(el, v.mul, &[xs[0], xs[1]]);
        (app(el, v.mul, &[xs[0], sy]), app(el, v.add, &[r, xs[0]]))
    })?);
    let gv = el.g.env.var(0);
    let targs = [gv, el.tr(v.mul)?, el.tr(v.add)?];
    mm(el.g.env.thm_n("mul_eqs_i", &targs, &hyps))
}

/// The carried proof `name` as a term `h` with `⟦ₜ G ⊢ h : ty ⟧`: a premise asking that a
/// proof of `ty` exists.
fn proof<'t>(el: &mut El<'_, '_, 't, '_>, b: &mut Baked<'t>, name: &str, ty: Ex<'t>) -> R<(E, P)> {
    let h = b.term(el, name)?;
    let (t, p) = el.infer(h).map_err(|e| format!("the proof `{name}`: {e}"))?;
    let p = el.cast(p, t, ty).map_err(|e| format!("the statement of the proof `{name}`: {e}"))?;
    Ok((el.tr(h)?, p))
}

// ------------------------------------------------------------------ the relations

/// `divmod_eqs G fd fm fmul fadd` for `pair`: proofs of `y * (x / y) + x % y = x`,
/// `0 < y → x % y < y` and `x / 0 = 0`.
fn divmod<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, b: &mut Baked<'t>, pair: Pair, mut targs: Vec<E>) -> R<P> {
    let mut hyps = vec![mul_eqs(el, v)?, closed(el, v.div)?, closed(el, v.mod_)?, binop(el, v, v.div)?, binop(el, v, v.mod_)?];
    let (x, y) = (el.tc.ctx.mk_var(1), el.tc.ctx.mk_var(0));
    let ty1 = {
        let q = app(el, v.div, &[x, y]);
        let (m, r) = (app(el, v.mul, &[y, q]), app(el, v.mod_, &[x, y]));
        let s = app(el, v.add, &[m, r]);
        let e = v.eq(el, s, x);
        v.pi2(el, e)
    };
    let ty2 = {
        // under `h : 0 < y`: `x` is `#2`, `y` is `#1`
        let (x1, y1) = (el.tc.ctx.mk_var(2), el.tc.ctx.mk_var(1));
        let r = app(el, v.mod_, &[x1, y1]);
        let concl = v.lt(el, r, y1);
        let pos = v.lt(el, v.lits[0], y);
        let e = pi(el, "h", pos, concl);
        v.pi2(el, e)
    };
    let ty3 = {
        let q = app(el, v.div, &[y, v.lits[0]]);
        let e = v.eq(el, q, v.lits[0]);
        pi(el, "x", v.nat, e)
    };
    for (name, ty) in pair.proofs().into_iter().zip([ty1, ty2, ty3]) {
        let (h, p) = proof(el, b, name, ty)?;
        targs.push(h);
        hyps.push(p);
    }
    mm(el.g.env.thm_n("divmod_eqs_i", &targs, &hyps))
}

/// `gcd_eqs G gcd fd fm fmul fadd`: proofs of `gcd 0 y = y` and
/// `gcd (x + 1) y = gcd (y % (x + 1)) (x + 1)`.
fn gcd<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, b: &mut Baked<'t>, o: &Op, mut targs: Vec<E>) -> R<P> {
    let f = konst(el, "Nat.gcd", &[])?;
    let mut hyps = vec![fact(el, o.pair.key())?, closed(el, f)?, typing(el, "Nat.gcd")?];
    let (x, y) = (el.tc.ctx.mk_var(1), el.tc.ctx.mk_var(0));
    let ty1 = {
        let l = app(el, f, &[v.lits[0], y]);
        let e = v.eq(el, l, y);
        pi(el, "y", v.nat, e)
    };
    let ty2 = {
        let sx = app(el, v.succ, &[x]);
        let l = app(el, f, &[sx, y]);
        let m = app(el, v.mod_, &[y, sx]);
        let r = app(el, f, &[m, sx]);
        let e = v.eq(el, l, r);
        v.pi2(el, e)
    };
    for (name, ty) in [("gcd_zero", ty1), ("gcd_succ", ty2)] {
        let (h, p) = proof(el, b, name, ty)?;
        targs.push(h);
        hyps.push(p);
    }
    mm(el.g.env.thm_n("gcd_eqs_i", &targs, &hyps))
}

/// `land_eqs G f fd fm fmul fadd` (and `lor_eqs`, `xor_eqs`): a proof of
/// `f x y = f (x/2) (y/2) + f (x/2) (y/2) + bit`, where `bit` is `(x%2 + y%2) / 2` for
/// and, `(x%2 + y%2 + 1) / 2` for or and `(x%2 + y%2) % 2` for xor.
fn bitop<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, b: &mut Baked<'t>, o: &Op, mut targs: Vec<E>) -> R<P> {
    let f = konst(el, o.lean, &[])?;
    let mut hyps = vec![fact(el, o.pair.key())?, closed(el, f)?, typing(el, o.lean)?];
    let (x, y) = (el.tc.ctx.mk_var(1), el.tc.ctx.mk_var(0));
    let [_, one, two] = v.lits;
    let ty = {
        let (hx, hy) = (app(el, v.div, &[x, two]), app(el, v.div, &[y, two]));
        let l = app(el, f, &[hx, hy]);
        let ll = app(el, v.add, &[l, l]);
        let (bx, by) = (app(el, v.mod_, &[x, two]), app(el, v.mod_, &[y, two]));
        let s = app(el, v.add, &[bx, by]);
        let bit = match o.lean {
            "Nat.land" => app(el, v.div, &[s, two]),
            "Nat.lor" => {
                let s1 = app(el, v.add, &[s, one]);
                app(el, v.div, &[s1, two])
            }
            _ => app(el, v.mod_, &[s, two]),
        };
        let r = app(el, v.add, &[ll, bit]);
        let l = app(el, f, &[x, y]);
        let e = v.eq(el, l, r);
        v.pi2(el, e)
    };
    let name = match o.lean {
        "Nat.land" => "land_rec",
        "Nat.lor" => "lor_rec",
        _ => "xor_rec",
    };
    let (h, p) = proof(el, b, name, ty)?;
    targs.push(h);
    hyps.push(p);
    mm(el.g.env.thm_n(&format!("{}_i", o.rel), &targs, &hyps))
}

// ------------------------------------------------------------------ the theorems

/// The arguments of `o`'s relation after `G` (as the `_eqs` theorem and the `_lit` rules
/// take them): the operation unless it is one of the pair, then the pair, the
/// multiplication and `Nat.add`. Statements must not depend on proving, so this only builds
/// terms.
pub fn rel_args(el: &mut El<'_, '_, '_, '_>, o: &Op) -> R<Vec<E>> {
    let mut b = Baked::default();
    let v = Voc::new(el, &mut b, o.pair)?;
    let mut args = Vec::new();
    if o.rel != "divmod_eqs" {
        let f = konst(el, o.lean, &[])?;
        args.push(el.tr(f)?);
    }
    args.extend(v.divmod_args(el)?);
    Ok(args)
}

/// State `rel G args` as the theorem `name`, proved by `derive` unless this is a replay.
fn state(el: &mut El<'_, '_, '_, '_>, name: &str, rel: &str, args: &[E], doc: &str, derive: impl FnOnce(&mut El<'_, '_, '_, '_>, Vec<E>) -> R<P>) -> R<ThId> {
    let g = &mut *el.g;
    let mut targs = vec![g.env.var(0)];
    targs.extend(args);
    let concl = g.env.app_n(rel, &targs);
    let name = g.thms.fresh(name);
    let args_g = g.g_args(&[]);
    if g.replay {
        return add_thm(&mut g.env, &name, args_g, vec![], concl, false, false, None, doc)
    }
    if el.depth() != 0 {
        return Err("internal: the equations are derived at the top level".into())
    }
    // the proofs are about the definitions, not the kernel's computation on literals, which
    // for these operations is what they justify
    el.tc.nat_ops_off = true;
    let r = derive(el, targs);
    el.tc.nat_ops_off = false;
    let p = r?;
    add_thm(&mut el.g.env, &name, args_g, vec![], concl, false, false, Some(p), doc)
}

/// State `o`'s relation for the environment's definition as the theorem `{cname}_eqs`
/// (`cname`: the operation's MM0 constant), proved from the carried proofs. An operation
/// over Lean's `Nat.div` and `Nat.mod` both (the bitwise ones) first states their
/// `divmod_eqs`, once, as `{cname}_divmod`.
pub fn eqs_theorem(el: &mut El<'_, '_, '_, '_>, o: &'static Op, cname: &str) -> R<ThId> {
    let g = &*el.g;
    if let Some((c, _)) = BLOCKS.iter().find(|(c, d)| !(g.env.has_term(d) && g.consts.get(*c).is_some_and(|ci| ci.term == g.env.term_id(d)))) {
        return Err(format!("`{c}` is not declared as the spec has it"))
    }
    let args = rel_args(el, o)?;
    if o.rel != "divmod_eqs" && !el.g.nat_eqs.contains_key(o.pair.key()) {
        if o.pair != Pair::Both {
            return Err(format!("the equations of `{}` were not derived", o.pair.key()))
        }
        let doc = "`Nat.div` and `Nat.mod` have proofs of the equations the spec's `divmod_eqs` asks for.";
        let pair = o.pair;
        let th = state(el, &format!("{cname}_divmod"), "divmod_eqs", &args[1..], doc, |el, targs| {
            let mut b = Baked::default();
            let v = Voc::new(el, &mut b, pair)?;
            divmod(el, &v, &mut b, pair, targs)
        })?;
        el.g.nat_eqs.insert(pair.key().to_string(), th);
    }
    let doc = format!("`{}` has proofs of the equations the spec's `{}` asks for.", o.lean, o.rel);
    state(el, &format!("{cname}_eqs"), o.rel, &args, &doc, |el, targs| {
        let mut b = Baked::default();
        let v = Voc::new(el, &mut b, o.pair)?;
        match o.rel {
            "divmod_eqs" => divmod(el, &v, &mut b, o.pair, targs),
            "gcd_eqs" => gcd(el, &v, &mut b, o, targs),
            _ => bitop(el, &v, &mut b, o, targs),
        }
    })
}
