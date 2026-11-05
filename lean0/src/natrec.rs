//! The division-like literal operations (audit §5, stage B): `Nat.div`, `Nat.mod`, `Nat.gcd`
//! and, through `Nat.bitwise`, `Nat.land`, `Nat.lor` and `Nat.xor`. Their defining equations
//! go through conditionals on decided propositions (`dite`, `ite`, `Decidable`), fuel
//! recursion (`Nat.div.go`, `Nat.modCore.go`) and the well-founded fixpoint
//! `WellFounded.Nat.fix`. The spec's relations `dec_eqs`, `natle_dec`, `nateq_dec`,
//! `bool_dec`, `fix_eqs`, `div_eqs`, `mod_eqs`, `gcd_eqs`, `bitwise_eqs` and `bitop_eqs` state
//! Lean4Lean's checks of them (`Condition.check`, `checkNatDITE`, `checkITE`,
//! `checkNatFuelRec`, `unfoldNatWellFounded` and the probes of `checkNatGcd` and
//! `checkNatBitwise`) over variables standing for Lean's `@dite Nat`, `Decidable.intro`,
//! `Nat.decLe`, the proof terms, and so on. This module builds those terms by name
//! (`Voc`), reads the fixpoint's parts off the `_unary` definitions (`Wf`), derives each
//! relation's premises with the elaborator over fresh variables, and states the operation's
//! `_eqs` theorem (`eqs_theorem`); `natlit::op_axioms` then proves the `_lit` theorems from
//! the spec's rules.

use crate::elab::{mm, Elab, R};
use crate::gen::add_thm;
use crate::natlit;
use mm0kit::env::{ThId, E, P};
use nanoda_lib::expr::{BinderStyle, Expr};
use nanoda_lib::util::{ExprPtr, LevelPtr, NamePtr};
use num_bigint::BigUint;

/// An operation with a relation in the spec, and the operations whose relations its own
/// takes as premises (their `_eqs` theorems must have been derived).
pub struct Op {
    pub lean: &'static str,
    pub rel: &'static str,
    pub deps: &'static [&'static str],
}

pub const OPS: &[Op] = &[
    Op { lean: "Nat.div", rel: "div_eqs", deps: &["Nat.ble", "Nat.sub"] },
    Op { lean: "Nat.mod", rel: "mod_eqs", deps: &["Nat.ble", "Nat.sub"] },
    Op { lean: "Nat.gcd", rel: "gcd_eqs", deps: &["Nat.mod", "Nat.beq"] },
    Op { lean: "Nat.bitwise", rel: "bitwise_eqs", deps: &["Nat.div", "Nat.mod", "Nat.beq", "Nat.add"] },
    Op { lean: "Nat.land", rel: "bitop_eqs", deps: &["Nat.bitwise"] },
    Op { lean: "Nat.lor", rel: "bitop_eqs", deps: &["Nat.bitwise"] },
    Op { lean: "Nat.xor", rel: "bitop_eqs", deps: &["Nat.bitwise"] },
];

pub fn op(lean: &str) -> Option<&'static Op> { OPS.iter().find(|o| o.lean == lean) }

type Ex<'t> = ExprPtr<'t>;
type El<'a, 'x, 't, 'p> = Elab<'a, 'x, 't, 'p>;

// ------------------------------------------------------------------ terms

fn name<'t>(el: &mut El<'_, '_, 't, '_>, s: &str) -> R<NamePtr<'t>> {
    el.tc.ctx.export_file.find_name(s).ok_or_else(|| format!("no `{s}`"))
}

fn konst<'t>(el: &mut El<'_, '_, 't, '_>, s: &str, ls: &[LevelPtr<'t>]) -> R<Ex<'t>> {
    let n = name(el, s)?;
    let ls = el.tc.ctx.alloc_levels_slice(ls);
    Ok(el.tc.ctx.mk_const(n, ls))
}

fn app<'t>(el: &mut El<'_, '_, 't, '_>, f: Ex<'t>, args: &[Ex<'t>]) -> Ex<'t> {
    args.iter().fold(f, |f, &a| el.tc.ctx.mk_app(f, a))
}

fn lam<'t>(el: &mut El<'_, '_, 't, '_>, x: &'static str, ty: Ex<'t>, body: Ex<'t>) -> Ex<'t> {
    let n = el.tc.ctx.str1(x);
    el.tc.ctx.mk_lambda(n, BinderStyle::Default, ty, body)
}

fn pi<'t>(el: &mut El<'_, '_, 't, '_>, x: &'static str, ty: Ex<'t>, body: Ex<'t>) -> Ex<'t> {
    let n = el.tc.ctx.str1(x);
    el.tc.ctx.mk_pi(n, BinderStyle::Default, ty, body)
}

fn var<'t>(el: &mut El<'_, '_, 't, '_>, i: u16) -> Ex<'t> { el.tc.ctx.mk_var(i) }

fn open<'t>(el: &mut El<'_, '_, 't, '_>, x: &'static str, ty: Ex<'t>) -> R<Ex<'t>> {
    let n = el.tc.ctx.str1(x);
    el.open_pub(n, BinderStyle::Default, ty)
}

/// The derivation `Γ ⊢ lhs ≡ rhs : τ(lhs)` over the fresh variables `f` opens (closed
/// afterwards, also on failure).
fn eqn<'t, F>(el: &mut El<'_, '_, 't, '_>, f: F) -> R<P>
where
    F: FnOnce(&mut El<'_, '_, 't, '_>) -> R<(Ex<'t>, Ex<'t>)>,
{
    eqn_at(el, |el| f(el).map(|(lhs, rhs)| (lhs, rhs, None)))
}

/// As `eqn`, at the type `f` gives (`τ(lhs)` may be a redex of it, e.g. `(λ _. Nat) a`
/// for an application of the fixpoint's measure).
fn eqn_at<'t, F>(el: &mut El<'_, '_, 't, '_>, f: F) -> R<P>
where
    F: FnOnce(&mut El<'_, '_, 't, '_>) -> R<(Ex<'t>, Ex<'t>, Option<Ex<'t>>)>,
{
    let d0 = el.depth();
    let r = f(el).and_then(|(lhs, rhs, ty)| {
        let p = el.defeq(lhs, rhs)?;
        match ty {
            Some(ty) => {
                let from = el.infer(lhs)?.0;
                el.cast(p, from, ty)
            }
            None => Ok(p),
        }
    });
    while el.depth() > d0 {
        el.close_pub();
    }
    r
}

/// `closed z e`.
fn closed<'t>(el: &mut El<'_, '_, 't, '_>, e: Ex<'t>) -> R<P> {
    let m = el.tr(e)?;
    let g = &mut *el.g;
    let zk = g.lean.nat(&mut g.env, 0);
    mm(g.lean.closed(&mut g.env, zk, m))
}

fn closed_all<'t>(el: &mut El<'_, '_, 't, '_>, es: &[Ex<'t>]) -> R<Vec<P>> { es.iter().map(|&e| closed(el, e)).collect() }

/// The `_eqs` theorem of `lean`, at `G`.
fn fact(el: &mut El<'_, '_, '_, '_>, lean: &str) -> R<P> {
    let Some(&th) = el.g.nat_eqs.get(lean) else { return Err(format!("the equations of `{lean}` were not derived")) };
    let gv = el.g.env.var(0);
    mm(el.g.env.thm(th, &[gv], &[]))
}

/// `⟨ G ⊢ c : T ⟩` for the constant `lean`, from its typing lemma.
fn typing(el: &mut El<'_, '_, '_, '_>, lean: &str) -> R<P> {
    let th = el.g.consts[lean].ty_thm;
    let gv = el.g.env.var(0);
    mm(el.g.env.thm(th, &[gv], &[]))
}

/// `⟨ G ⊢ e : ty ⟩`, from `e`'s inferred type: a premise stating the type of a helper the
/// equations apply (audit §5: the instances are taken at its values).
fn typed<'t>(el: &mut El<'_, '_, 't, '_>, e: Ex<'t>, ty: Ex<'t>) -> R<P> {
    let (t, p) = el.infer(e)?;
    el.cast(p, t, ty)
}

/// `Bool → Bool → Bool`.
fn bool_fn<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>) -> Ex<'t> {
    let inner = pi(el, "y", v.bool_, v.bool_);
    pi(el, "x", v.bool_, inner)
}

/// `Π x y : Nat. body` with `body` built at depth 2 (`y` is `#0`, `x` is `#1`).
fn pi_nat2<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, body: Ex<'t>) -> Ex<'t> {
    let inner = pi(el, "y", v.nat, body);
    pi(el, "x", v.nat, inner)
}

fn rule<'t>(el: &mut El<'_, '_, 't, '_>, rel: &str, args: &[Ex<'t>], hyps: &[P]) -> R<P> {
    let mut targs = vec![el.g.env.var(0)];
    for &a in args {
        targs.push(el.tr(a)?);
    }
    mm(el.g.env.thm_n(&format!("{rel}_i"), &targs, hyps))
}

// ------------------------------------------------------------------ the vocabulary

/// The terms the relations are about, built by name: the decision reflection (the
/// `dec_eqs` arguments `d`), the three conditions, and the functions the equations mention.
struct Voc<'t> {
    nat: Ex<'t>,
    bool_: Ex<'t>,
    tt: Ex<'t>,
    ff: Ex<'t>,
    not: Ex<'t>,
    /// `Decidable`.
    dec_ty: Ex<'t>,
    /// `@dite.{1} Nat`, `@ite.{1} Nat`.
    dite: Ex<'t>,
    ite: Ex<'t>,
    /// `T = λ p b. Bool.Reflects b p`, `R = Decidable.intro`, `ofT = ofF = λ p H. H`.
    refl: Ex<'t>,
    intro: Ex<'t>,
    of_t: Ex<'t>,
    of_f: Ex<'t>,
    /// `@LE.le Nat _`, `Nat.decLe`, `Nat.ble`, `λ x y. Decidable.reflects_decide (x ≤ y) _`.
    le: Ex<'t>,
    dle: Ex<'t>,
    ble: Ex<'t>,
    pf_le: Ex<'t>,
    /// `@Eq Nat`, `Nat.decEq`, `Nat.beq`, and the proof as for `le`.
    eq: Ex<'t>,
    deq: Ex<'t>,
    beq: Ex<'t>,
    pf_eq: Ex<'t>,
    /// `λ b : Bool. b = true` and `λ b. instDecidableEqBool b true`.
    bp: Ex<'t>,
    bd: Ex<'t>,
    /// `@LT.lt Nat _`, `Decidable.decide`.
    lt: Ex<'t>,
    decide: Ex<'t>,
    prop: Ex<'t>,
    succ: Ex<'t>,
    lit0: Ex<'t>,
    lit1: Ex<'t>,
    lit2: Ex<'t>,
}

impl<'t> Voc<'t> {
    fn new(el: &mut El<'_, '_, 't, '_>) -> R<Self> {
        let zero = el.tc.ctx.zero();
        let one = el.tc.ctx.succ(zero);
        let (nat, bool_) = (konst(el, "Nat", &[])?, konst(el, "Bool", &[])?);
        let (tt, ff, not) = (konst(el, "Bool.true", &[])?, konst(el, "Bool.false", &[])?, konst(el, "Not", &[])?);
        let dec_ty = konst(el, "Decidable", &[])?;
        let (dite, ite) = (konst(el, "dite", &[one])?, konst(el, "ite", &[one])?);
        let (dite, ite) = (app(el, dite, &[nat]), app(el, ite, &[nat]));
        let prop = el.tc.ctx.mk_sort(zero);
        let reflects = konst(el, "Bool.Reflects", &[])?;
        let refl = {
            let (p, b) = (var(el, 1), var(el, 0));
            let body = app(el, reflects, &[b, p]);
            let inner = lam(el, "b", bool_, body);
            lam(el, "p", prop, inner)
        };
        let intro = konst(el, "Decidable.intro", &[])?;
        let of = |el: &mut El<'_, '_, 't, '_>, b: Ex<'t>| {
            let p = var(el, 0);
            let hty = app(el, reflects, &[b, p]);
            let h = var(el, 0);
            let inner = lam(el, "H", hty, h);
            lam(el, "p", prop, inner)
        };
        let (of_t, of_f) = (of(el, tt), of(el, ff));
        let (le, inst_le) = (konst(el, "LE.le", &[zero])?, konst(el, "instLENat", &[])?);
        let le = app(el, le, &[nat, inst_le]);
        let (lt, inst_lt) = (konst(el, "LT.lt", &[zero])?, konst(el, "instLTNat", &[])?);
        let lt = app(el, lt, &[nat, inst_lt]);
        let (dle, ble) = (konst(el, "Nat.decLe", &[])?, konst(el, "Nat.ble", &[])?);
        let eq = konst(el, "Eq", &[one])?;
        let eqn_ = app(el, eq, &[nat]);
        let (deq, beq) = (konst(el, "Nat.decEq", &[])?, konst(el, "Nat.beq", &[])?);
        let reflects_decide = konst(el, "Decidable.reflects_decide", &[])?;
        // `λ x y : Nat. Decidable.reflects_decide (r x y) (d x y)`
        let pf = |el: &mut El<'_, '_, 't, '_>, r: Ex<'t>, d: Ex<'t>| {
            let (x, y) = (var(el, 1), var(el, 0));
            let (rxy, dxy) = (app(el, r, &[x, y]), app(el, d, &[x, y]));
            let body = app(el, reflects_decide, &[rxy, dxy]);
            let inner = lam(el, "y", nat, body);
            lam(el, "x", nat, inner)
        };
        let (pf_le, pf_eq) = (pf(el, le, dle), pf(el, eqn_, deq));
        let bp = {
            let b = var(el, 0);
            let body = app(el, eq, &[bool_, b, tt]);
            lam(el, "b", bool_, body)
        };
        let bd = {
            let deqb = konst(el, "instDecidableEqBool", &[])?;
            let b = var(el, 0);
            let body = app(el, deqb, &[b, tt]);
            lam(el, "b", bool_, body)
        };
        let decide = konst(el, "Decidable.decide", &[])?;
        let succ = konst(el, "Nat.succ", &[])?;
        let lit = |el: &mut El<'_, '_, 't, '_>, n: u32| {
            el.tc.ctx.mk_nat_lit_quick(BigUint::from(n)).ok_or_else(|| format!("internal: no literal {n}"))
        };
        let (lit0, lit1, lit2) = (lit(el, 0)?, lit(el, 1)?, lit(el, 2)?);
        Ok(Voc {
            nat,
            bool_,
            tt,
            ff,
            not,
            dec_ty,
            dite,
            ite,
            refl,
            intro,
            of_t,
            of_f,
            le,
            dle,
            ble,
            pf_le,
            eq: eqn_,
            deq,
            beq,
            pf_eq,
            bp,
            bd,
            lt,
            decide,
            prop,
            succ,
            lit0,
            lit1,
            lit2,
        })
    }

    /// The arguments of `dec_eqs` after `G`: `B t u Not Dec dite T R ofT ofF`.
    fn d(&self) -> [Ex<'t>; 10] {
        [self.bool_, self.tt, self.ff, self.not, self.dec_ty, self.dite, self.refl, self.intro, self.of_t, self.of_f]
    }

    /// The arguments of `ite_eqs` after `G`: `B t u T R ite`.
    fn ite_args(&self) -> [Ex<'t>; 6] { [self.bool_, self.tt, self.ff, self.refl, self.intro, self.ite] }

    fn natle(&self) -> [Ex<'t>; 4] { [self.le, self.dle, self.ble, self.pf_le] }

    fn nateq(&self) -> [Ex<'t>; 4] { [self.eq, self.deq, self.beq, self.pf_eq] }

    /// The arguments of `bool_dec` after `G`.
    fn bool_dec(&self) -> [Ex<'t>; 8] { [self.bool_, self.tt, self.ff, self.not, self.dite, self.ite, self.bp, self.bd] }

    /// `R p b H`.
    fn r(&self, el: &mut El<'_, '_, 't, '_>, p: Ex<'t>, b: Ex<'t>, h: Ex<'t>) -> Ex<'t> { app(el, self.intro, &[p, b, h]) }

    /// `T p b`.
    fn t(&self, el: &mut El<'_, '_, 't, '_>, p: Ex<'t>, b: Ex<'t>) -> Ex<'t> { app(el, self.refl, &[p, b]) }

    fn s(&self, el: &mut El<'_, '_, 't, '_>, x: Ex<'t>) -> Ex<'t> { app(el, self.succ, &[x]) }

    /// `Not p`.
    fn no(&self, el: &mut El<'_, '_, 't, '_>, p: Ex<'t>) -> Ex<'t> { app(el, self.not, &[p]) }

    /// `dite P D (λ _ : P. a) (λ _ : Not P. b)`.
    fn dite_const(&self, el: &mut El<'_, '_, 't, '_>, p: Ex<'t>, d: Ex<'t>, a: Ex<'t>, b: Ex<'t>) -> Ex<'t> {
        let np = self.no(el, p);
        let (la, lb) = (lam(el, "h", p, a), lam(el, "h", np, b));
        app(el, self.dite, &[p, d, la, lb])
    }
}

// ------------------------------------------------------------------ the fixpoint

/// `WellFounded.Nat.fix` as a `_unary` definition applies it: `fix al motive hm F` under
/// `nlam` leading binders (`Nat.bitwise._unary` abstracts the Bool function).
struct Wf<'t> {
    fix: Ex<'t>,
    go: Ex<'t>,
    eager: Ex<'t>,
    al: Ex<'t>,
    motive: Ex<'t>,
    hm: Ex<'t>,
    /// `WellFounded.Nat.fix._proof_2 al hm` and `_proof_1 al hm`.
    pfx: Ex<'t>,
    pfgo: Ex<'t>,
    /// The functional, under the leading binders (`F` for `gcd`, `λ f. F` for `bitwise`).
    f_lam: Ex<'t>,
    /// The functional itself, the leading binders open as loose bound variables.
    f: Ex<'t>,
}

/// `e` under `n` leading lambdas: the binders and the body.
fn strip_lams<'t>(el: &mut El<'_, '_, 't, '_>, mut e: Ex<'t>, n: usize) -> R<(Vec<(NamePtr<'t>, BinderStyle, Ex<'t>)>, Ex<'t>)> {
    let mut bs = Vec::new();
    for _ in 0..n {
        let Expr::Lambda { binder_name, binder_style, binder_type, body, .. } = el.tc.ctx.read_expr(e) else {
            return Err("internal: the definition has fewer binders than expected".into())
        };
        bs.push((binder_name, binder_style, binder_type));
        e = body;
    }
    Ok((bs, e))
}

fn value<'t>(el: &mut El<'_, '_, 't, '_>, lean: &str) -> R<Ex<'t>> {
    let n = name(el, lean)?;
    Ok(el.tc.env.get_declar_val(&n).ok_or_else(|| format!("`{lean}` is not a definition"))?.1)
}

fn wf<'t>(el: &mut El<'_, '_, 't, '_>, unary: &str, nlam: usize) -> R<Wf<'t>> {
    let v = value(el, unary)?;
    let (bs, body) = strip_lams(el, v, nlam)?;
    let (head, args) = el.tc.ctx.unfold_apps(body);
    let fix_name = name(el, "WellFounded.Nat.fix")?;
    let Expr::Const { name: hn, levels, .. } = el.tc.ctx.read_expr(head) else { return Err(format!("`{unary}` is not a fixpoint")) };
    if hn != fix_name || args.len() != 4 {
        return Err(format!("`{unary}` is not `WellFounded.Nat.fix al motive hm F`"))
    }
    let ls: Vec<LevelPtr<'t>> = el.tc.ctx.read_levels(levels).to_vec();
    let (al, motive, hm, f) = (args[0], args[1], args[2], args[3]);
    let go = konst(el, "WellFounded.Nat.fix.go", &ls)?;
    let eager = konst(el, "WellFounded.Nat.eager", &[])?;
    let (p2, p1) = (konst(el, "WellFounded.Nat.fix._proof_2", &ls[..1])?, konst(el, "WellFounded.Nat.fix._proof_1", &ls[..1])?);
    let (pfx, pfgo) = (app(el, p2, &[al, hm]), app(el, p1, &[al, hm]));
    let mut f_lam = f;
    for &(n, s, ty) in bs.iter().rev() {
        f_lam = el.tc.ctx.mk_lambda(n, s, ty, f_lam);
    }
    Ok(Wf { fix: head, go, eager, al, motive, hm, pfx, pfgo, f_lam, f })
}

impl<'t> Wf<'t> {
    /// `fix_fty al motive hm lt`: the type of a functional.
    fn fty(&self, el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>) -> Ex<'t> {
        let (y, x) = (var(el, 0), var(el, 1));
        let (hy, hx) = (app(el, self.hm, &[y]), app(el, self.hm, &[x]));
        let lt = app(el, v.lt, &[hy, hx]);
        let y1 = var(el, 1);
        let my = app(el, self.motive, &[y1]);
        let ih_body = pi(el, "hy", lt, my);
        let ih = pi(el, "y", self.al, ih_body);
        let x1 = var(el, 1);
        let mx = app(el, self.motive, &[x1]);
        let body = pi(el, "ih", ih, mx);
        pi(el, "x", self.al, body)
    }

    /// The type of the recursion argument `ih` at the packed argument `a`:
    /// `Π y : al. lt (hm y) (hm a) → motive y`.
    fn ih_ty(&self, el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, a: Ex<'t>) -> Ex<'t> {
        let y = var(el, 0);
        let (hy, ha) = (app(el, self.hm, &[y]), app(el, self.hm, &[a]));
        let lt = app(el, v.lt, &[hy, ha]);
        let y1 = var(el, 1);
        let my = app(el, self.motive, &[y1]);
        let body = pi(el, "hy", lt, my);
        pi(el, "y", self.al, body)
    }
}

/// The arguments of `fix_eqs` after `G`: `ite bp bd beq fix go eager al motive hm lt pfx pfgo`.
fn fix_args<'t>(v: &Voc<'t>, w: &Wf<'t>) -> Vec<Ex<'t>> {
    vec![v.ite, v.bp, v.bd, v.beq, w.fix, w.go, w.eager, w.al, w.motive, w.hm, v.lt, w.pfx, w.pfgo]
}

/// `λ n m : Nat. a`, where the definition `lean` (under `nlam` binders, the last two the
/// arguments) is `_unary ... a`: the packing of the arguments.
fn pack<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, lean: &str, nlam: usize) -> R<Ex<'t>> {
    let val = value(el, lean)?;
    let (_, body) = strip_lams(el, val, nlam)?;
    let (_, args) = el.tc.ctx.unfold_apps(body);
    let Some(&a) = args.last() else { return Err(format!("`{lean}` does not apply its `_unary`")) };
    let inner = lam(el, "m", v.nat, a);
    Ok(lam(el, "n", v.nat, inner))
}

/// The lemma a functional's recursive call `ih a (c ...)` applies for the measure's
/// decrease: `F` is `λ x ih. PSigma.casesOn ... x (λ n m ih. body) ih`, and `c` heads the
/// second argument of the first application of `ih` in `body`.
fn probe_proof<'t>(el: &mut El<'_, '_, 't, '_>, f: Ex<'t>) -> R<Ex<'t>> {
    let (_, body) = strip_lams(el, f, 2)?;
    let (head, args) = el.tc.ctx.unfold_apps(body);
    let cases = name(el, "PSigma.casesOn")?;
    if !matches!(el.tc.ctx.read_expr(head), Expr::Const { name, .. } if name == cases) || args.len() != 6 {
        return Err("the functional is not a `PSigma.casesOn`".into())
    }
    let (_, body) = strip_lams(el, args[4], 3)?;
    fn find<'t>(el: &mut El<'_, '_, 't, '_>, e: Ex<'t>, depth: u16) -> Option<Ex<'t>> {
        match el.tc.ctx.read_expr(e) {
            Expr::App { fun, arg, .. } => {
                if let Expr::App { fun: f2, .. } = el.tc.ctx.read_expr(fun) {
                    if matches!(el.tc.ctx.read_expr(f2), Expr::Var { dbj_idx, .. } if dbj_idx == depth) {
                        return Some(arg)
                    }
                }
                find(el, fun, depth).or_else(|| find(el, arg, depth))
            }
            Expr::Lambda { binder_type, body, .. } | Expr::Pi { binder_type, body, .. } => {
                find(el, binder_type, depth).or_else(|| find(el, body, depth + 1))
            }
            Expr::Let { binder_type, val, body, .. } => {
                find(el, binder_type, depth).or_else(|| find(el, val, depth)).or_else(|| find(el, body, depth + 1))
            }
            _ => None,
        }
    }
    let Some(p) = find(el, body, 0) else { return Err("no recursive call in the functional".into()) };
    let c = el.tc.ctx.unfold_apps_fun(p);
    if !matches!(el.tc.ctx.read_expr(c), Expr::Const { .. }) {
        return Err("the recursive call's proof is not a lemma applied".into())
    }
    Ok(c)
}

// ------------------------------------------------------------------ the relations

/// `dec_eqs G B t u Not Dec dite T R ofT ofF` (`dite`), or `ite_eqs G B t u T R ite`.
fn dec_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, dite: bool) -> R<P> {
    let args: Vec<Ex<'t>> = if dite { v.d().to_vec() } else { v.ite_args().to_vec() };
    let mut hyps = closed_all(el, &args)?;
    if dite {
        // `ofT : Π p : Prop. T p t → p`, `ofF : Π p : Prop. T p u → Not p`
        for (of, b) in [(v.of_t, v.tt), (v.of_f, v.ff)] {
            let p0 = var(el, 0);
            let tpb = v.t(el, p0, b);
            let p1 = var(el, 1);
            let res = if b == v.tt { p1 } else { v.no(el, p1) };
            let inner = pi(el, "H", tpb, res);
            let ty = pi(el, "p", v.prop, inner);
            hyps.push(typed(el, of, ty)?);
        }
    }
    for b in [v.tt, v.ff] {
        hyps.push(eqn(el, |el| {
            let p = open(el, "p", v.prop)?;
            let tpb = v.t(el, p, b);
            let h = open(el, "H", tpb)?;
            let r = v.r(el, p, b, h);
            if dite {
                let np = v.no(el, p);
                let (ap, bp) = (pi(el, "h", p, v.nat), pi(el, "h", np, v.nat));
                let (a, bb) = (open(el, "a", ap)?, open(el, "b", bp)?);
                let lhs = app(el, v.dite, &[p, r, a, bb]);
                let (x, of) = if b == v.tt { (a, v.of_t) } else { (bb, v.of_f) };
                let ofph = app(el, of, &[p, h]);
                Ok((lhs, app(el, x, &[ofph])))
            } else {
                let (a, bb) = (open(el, "a", v.nat)?, open(el, "b", v.nat)?);
                let lhs = app(el, v.ite, &[p, r, a, bb]);
                Ok((lhs, if b == v.tt { a } else { bb }))
            }
        })?);
    }
    rule(el, if dite { "dec_eqs" } else { "ite_eqs" }, &args, &hyps)
}

/// `natle_dec G ... le dle ble pf` (`eq_dec: false`) or `nateq_dec G ... eq deq beq pq`.
fn cond_dec<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, eq_dec: bool) -> R<P> {
    let (rel, bool_op, [r, d, b, pf]) = if eq_dec { ("nateq_dec", "Nat.beq", v.nateq()) } else { ("natle_dec", "Nat.ble", v.natle()) };
    let mut hyps = vec![dec_eqs(el, v, true)?, fact(el, bool_op)?];
    hyps.extend(closed_all(el, &[r, d, pf])?);
    // `r : Nat → Nat → Prop`, `pf : Π x y. T (r x y) (b x y)`
    let rty = pi_nat2(el, v, v.prop);
    hyps.push(typed(el, r, rty)?);
    let (x, y) = (var(el, 1), var(el, 0));
    let (rxy, bxy) = (app(el, r, &[x, y]), app(el, b, &[x, y]));
    let tb = v.t(el, rxy, bxy);
    let pfty = pi_nat2(el, v, tb);
    hyps.push(typed(el, pf, pfty)?);
    hyps.push(eqn(el, |el| {
        let (x, y) = (open(el, "x", v.nat)?, open(el, "y", v.nat)?);
        let lhs = app(el, d, &[x, y]);
        let (rxy, bxy, pxy) = (app(el, r, &[x, y]), app(el, b, &[x, y]), app(el, pf, &[x, y]));
        Ok((lhs, v.r(el, rxy, bxy, pxy)))
    })?);
    let mut args = v.d().to_vec();
    args.extend([r, d, b, pf]);
    rule(el, rel, &args, &hyps)
}

/// `bool_dec G B t u Not dite ite bp bd`.
fn bool_dec<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>) -> R<P> {
    let args = v.bool_dec();
    let mut hyps = closed_all(el, &args)?;
    for (dite, b) in [(true, v.tt), (true, v.ff), (false, v.tt), (false, v.ff)] {
        hyps.push(eqn(el, |el| {
            let (a, bb) = (open(el, "a", v.nat)?, open(el, "b", v.nat)?);
            let (p, d) = (app(el, v.bp, &[b]), app(el, v.bd, &[b]));
            let lhs = if dite { v.dite_const(el, p, d, a, bb) } else { app(el, v.ite, &[p, d, a, bb]) };
            Ok((lhs, if b == v.tt { a } else { bb }))
        })?);
    }
    rule(el, "bool_dec", &args, &hyps)
}

/// The functions of `div_eqs`/`mod_eqs` after the decision and `sub` arguments: `f go pfs lem`.
struct Fuel<'t> {
    f: Ex<'t>,
    go: Ex<'t>,
    pfs: Ex<'t>,
    lem: Ex<'t>,
}

fn fuel<'t>(el: &mut El<'_, '_, 't, '_>, lean: &str) -> R<Fuel<'t>> {
    let go = if lean == "Nat.div" { "Nat.div.go" } else { "Nat.modCore.go" };
    Ok(Fuel {
        f: konst(el, lean, &[])?,
        go: konst(el, go, &[])?,
        pfs: konst(el, "Nat.lt_succ_self", &[])?,
        lem: konst(el, "Nat.div_rec_fuel_lemma", &[])?,
    })
}

fn fuel_args<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, u: &Fuel<'t>, is_mod: bool) -> R<Vec<E>> {
    let mut args = Vec::new();
    for a in v.d().iter().chain(&v.natle()) {
        args.push(el.tr(*a)?);
    }
    args.extend(natlit::rel_args(el, natlit::eqs("Nat.sub").unwrap()).ok_or("no `Nat.sub`")?);
    if is_mod {
        args.push(el.tr(v.ite)?);
    }
    for a in [u.f, u.go, u.pfs, u.lem] {
        args.push(el.tr(a)?);
    }
    Ok(args)
}

/// `div_eqs G ... f go pfs lem` or `mod_eqs ...` (`is_mod`).
fn fuel_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, u: &Fuel<'t>, lean: &str, targs: &[E]) -> R<P> {
    let is_mod = lean == "Nat.mod";
    let mut hyps = vec![cond_dec(el, v, false)?, fact(el, "Nat.sub")?];
    if is_mod {
        hyps.push(dec_eqs(el, v, false)?);
    }
    hyps.extend(closed_all(el, &[u.f, u.go, u.pfs, u.lem])?);
    hyps.push(typing(el, lean)?);
    let subc = konst(el, "Nat.sub", &[])?;
    {
        // `go : Π y. le 1 y → Π fuel x. le (succ x) fuel → Nat`
        let (x0, f1) = (var(el, 0), var(el, 1));
        let sx = v.s(el, x0);
        let h = app(el, v.le, &[sx, f1]);
        let body = pi(el, "h", h, v.nat);
        let body = pi(el, "x", v.nat, body);
        let body = pi(el, "fuel", v.nat, body);
        let y0 = var(el, 0);
        let hy = app(el, v.le, &[v.lit1, y0]);
        let body = pi(el, "hy", hy, body);
        let ty = pi(el, "y", v.nat, body);
        hyps.push(typed(el, u.go, ty)?);
        // `pfs : Π x. le (succ x) (succ x)`
        let x0 = var(el, 0);
        let sx = v.s(el, x0);
        let body = app(el, v.le, &[sx, sx]);
        let ty = pi(el, "x", v.nat, body);
        hyps.push(typed(el, u.pfs, ty)?);
        // `lem : Π x y fuel. le 1 y → le y x → le (succ x) (succ fuel) → le (succ (sub x y)) fuel`
        let (x5, y4, f3) = (var(el, 5), var(el, 4), var(el, 3));
        let sub = app(el, subc, &[x5, y4]);
        let ssub = v.s(el, sub);
        let res = app(el, v.le, &[ssub, f3]);
        let (x4, f2) = (var(el, 4), var(el, 2));
        let (sx, sf) = (v.s(el, x4), v.s(el, f2));
        let hfuel = app(el, v.le, &[sx, sf]);
        let body = pi(el, "hfuel", hfuel, res);
        let (y2, x3) = (var(el, 2), var(el, 3));
        let hle = app(el, v.le, &[y2, x3]);
        let body = pi(el, "hle", hle, body);
        let y1 = var(el, 1);
        let hy = app(el, v.le, &[v.lit1, y1]);
        let body = pi(el, "hy", hy, body);
        let body = pi(el, "fuel", v.nat, body);
        let ty = pi_nat2(el, v, body);
        hyps.push(typed(el, u.lem, ty)?);
    }
    if is_mod {
        hyps.push(eqn(el, |el| {
            let x = open(el, "x", v.nat)?;
            Ok((app(el, u.f, &[v.lit0, x]), v.lit0))
        })?);
    }
    // `λ hy : le 1 y. go y hy (succ x) x (pfs x)`, and `dite (le 1 y) (dle 1 y) that (λ _. e)`
    let top = |el: &mut El<'_, '_, 't, '_>, x: Ex<'t>, y: Ex<'t>, e: Ex<'t>| {
        let (p, d) = (app(el, v.le, &[v.lit1, y]), app(el, v.dle, &[v.lit1, y]));
        let (sx, psx, hy) = (v.s(el, x), app(el, u.pfs, &[x]), var(el, 0));
        let body = app(el, u.go, &[y, hy, sx, x, psx]);
        let then = lam(el, "hy", p, body);
        let np = v.no(el, p);
        let els = lam(el, "h", np, e);
        app(el, v.dite, &[p, d, then, els])
    };
    hyps.push(eqn(el, |el| {
        let (x, y) = (open(el, "x", v.nat)?, open(el, "y", v.nat)?);
        if is_mod {
            let sx = v.s(el, x);
            let lhs = app(el, u.f, &[sx, y]);
            let (p, d) = (app(el, v.le, &[y, sx]), app(el, v.dle, &[y, sx]));
            let inner = top(el, sx, y, sx);
            Ok((lhs, app(el, v.ite, &[p, d, inner, sx])))
        } else {
            let lhs = app(el, u.f, &[x, y]);
            Ok((lhs, top(el, x, y, v.lit0)))
        }
    })?);
    hyps.push(eqn(el, |el| {
        let (x, y) = (open(el, "x", v.nat)?, open(el, "y", v.nat)?);
        let hyt = app(el, v.le, &[v.lit1, y]);
        let hy = open(el, "hy", hyt)?;
        let fuel = open(el, "fuel", v.nat)?;
        let (sx, sf) = (v.s(el, x), v.s(el, fuel));
        let ht = app(el, v.le, &[sx, sf]);
        let h = open(el, "h", ht)?;
        let lhs = app(el, u.go, &[y, hy, sf, x, h]);
        let (p, d) = (app(el, v.le, &[y, x]), app(el, v.dle, &[y, x]));
        let h2 = var(el, 0);
        let subc = konst(el, "Nat.sub", &[])?;
        let (sub, lem) = (app(el, subc, &[x, y]), app(el, u.lem, &[x, y, fuel, hy, h2, h]));
        let call = app(el, u.go, &[y, hy, fuel, sub, lem]);
        let body = if is_mod { call } else { v.s(el, call) };
        let then = lam(el, "h2", p, body);
        let np = v.no(el, p);
        let els = lam(el, "h", np, if is_mod { x } else { v.lit0 });
        Ok((lhs, app(el, v.dite, &[p, d, then, els])))
    })?);
    mm(el.g.env.thm_n(&format!("{}_i", if is_mod { "mod_eqs" } else { "div_eqs" }), targs, &hyps))
}

/// `fix_eqs G ite bp bd beq fix go eager al motive hm lt pfx pfgo`.
fn fix_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, w: &Wf<'t>) -> R<P> {
    let args = fix_args(v, w);
    let mut hyps = closed_all(el, &args)?;
    // `lt : Nat → Nat → Prop`
    let ltty = pi_nat2(el, v, v.prop);
    hyps.push(typed(el, v.lt, ltty)?);
    // `go al motive hm : Π F : fix_fty. Π fuel x. lt (hm x) fuel → motive x`
    {
        let go3 = app(el, w.go, &[w.al, w.motive, w.hm]);
        let x1 = var(el, 1);
        let mx = app(el, w.motive, &[x1]);
        let (x0, f1) = (var(el, 0), var(el, 1));
        let hx = app(el, w.hm, &[x0]);
        let h = app(el, v.lt, &[hx, f1]);
        let body = pi(el, "h", h, mx);
        let body = pi(el, "x", w.al, body);
        let body = pi(el, "fuel", v.nat, body);
        let fty = w.fty(el, v);
        let ty = pi(el, "F", fty, body);
        hyps.push(typed(el, go3, ty)?);
        // `pfx : Π x : al. lt (hm x) (eager (succ (hm x)))`
        let x0 = var(el, 0);
        let hx = app(el, w.hm, &[x0]);
        let shx = v.s(el, hx);
        let eg = app(el, w.eager, &[shx]);
        let body = app(el, v.lt, &[hx, eg]);
        let ty = pi(el, "x", w.al, body);
        hyps.push(typed(el, w.pfx, ty)?);
        // `pfgo : Π t x. lt (hm x) (succ t) → Π y. lt (hm y) (hm x) → lt (hm y) t`
        let (y1, t4) = (var(el, 1), var(el, 4));
        let hy1 = app(el, w.hm, &[y1]);
        let res = app(el, v.lt, &[hy1, t4]);
        let (y0, x2) = (var(el, 0), var(el, 2));
        let (hy0, hx2) = (app(el, w.hm, &[y0]), app(el, w.hm, &[x2]));
        let hyt = app(el, v.lt, &[hy0, hx2]);
        let body = pi(el, "hy", hyt, res);
        let body = pi(el, "y", w.al, body);
        let (x0, t1) = (var(el, 0), var(el, 1));
        let hx0 = app(el, w.hm, &[x0]);
        let st = v.s(el, t1);
        let ht = app(el, v.lt, &[hx0, st]);
        let body = pi(el, "h", ht, body);
        let body = pi(el, "x", w.al, body);
        let ty = pi(el, "t", v.nat, body);
        hyps.push(typed(el, w.pfgo, ty)?);
    }
    hyps.push(eqn_at(el, |el| {
        let fty = w.fty(el, v);
        let (f, x) = (open(el, "F", fty)?, open(el, "x", w.al)?);
        let lhs = app(el, w.fix, &[w.al, w.motive, w.hm, f, x]);
        let hx = app(el, w.hm, &[x]);
        let shx = v.s(el, hx);
        let (fuel, px) = (app(el, w.eager, &[shx]), app(el, w.pfx, &[x]));
        let mx = app(el, w.motive, &[x]);
        Ok((lhs, app(el, w.go, &[w.al, w.motive, w.hm, f, fuel, x, px]), Some(mx)))
    })?);
    hyps.push(eqn(el, |el| {
        let x = open(el, "x", v.nat)?;
        let lhs = app(el, w.eager, &[x]);
        let bxx = app(el, v.beq, &[x, x]);
        let (p, d) = (app(el, v.bp, &[bxx]), app(el, v.bd, &[bxx]));
        Ok((lhs, app(el, v.ite, &[p, d, x, x])))
    })?);
    hyps.push(eqn_at(el, |el| {
        let fty = w.fty(el, v);
        let (f, t, x) = (open(el, "F", fty)?, open(el, "t", v.nat)?, open(el, "x", w.al)?);
        let (hx, st) = (app(el, w.hm, &[x]), v.s(el, t));
        let ht = app(el, v.lt, &[hx, st]);
        let h = open(el, "h", ht)?;
        let lhs = app(el, w.go, &[w.al, w.motive, w.hm, f, st, x, h]);
        // `λ y : al. λ hy : lt (hm y) (hm x). go al motive hm F t y (pfgo t x h y hy)`
        let y0 = var(el, 0);
        let hy0 = app(el, w.hm, &[y0]);
        let hyt = app(el, v.lt, &[hy0, hx]);
        let (y, hy) = (var(el, 1), var(el, 0));
        let pf = app(el, w.pfgo, &[t, x, h, y, hy]);
        let call = app(el, w.go, &[w.al, w.motive, w.hm, f, t, y, pf]);
        let inner = lam(el, "hy", hyt, call);
        let ih = lam(el, "y", w.al, inner);
        let mx = app(el, w.motive, &[x]);
        Ok((lhs, app(el, f, &[x, ih]), Some(mx)))
    })?);
    rule(el, "fix_eqs", &args, &hyps)
}

/// A definition by `WellFounded.Nat.fix` over packed arguments (`Nat.gcd`, `Nat.bitwise`):
/// the fixpoint, the definition, the packing and the recursive call's lemma.
struct Rec<'t> {
    w: Wf<'t>,
    f: Ex<'t>,
    pack: Ex<'t>,
    /// The lemma of the recursive call (`pfF`, `pfB`).
    pf: Ex<'t>,
}

fn rec_parts<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, lean: &str) -> R<Rec<'t>> {
    let bitwise = lean == "Nat.bitwise";
    let nlam = if bitwise { 1 } else { 0 };
    let w = wf(el, &format!("{lean}._unary"), nlam)?;
    let pack = pack(el, v, lean, nlam + 2)?;
    let pf = probe_proof(el, w.f)?;
    Ok(Rec { w, f: konst(el, lean, &[])?, pack, pf })
}

/// `pack : Nat → Nat → al` and the recursive call's lemma
/// `pf : Π a b. Not (a = 0) → lt (hm (pack a' b')) (hm (pack a b))`, with `(a', b')` the
/// call's arguments (`next a b`, built at the depth of the lemma's result).
fn rec_typings<'t, N>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>, next: N) -> R<Vec<P>>
where
    N: FnOnce(&mut El<'_, '_, 't, '_>, Ex<'t>, Ex<'t>) -> R<(Ex<'t>, Ex<'t>)>,
{
    let w = &r.w;
    let packty = pi_nat2(el, v, w.al);
    let p1 = typed(el, r.pack, packty)?;
    let (a2, b1) = (var(el, 2), var(el, 1));
    let (na, nb) = next(el, a2, b1)?;
    let (pn, pab) = (app(el, r.pack, &[na, nb]), app(el, r.pack, &[a2, b1]));
    let (hn, hab) = (app(el, w.hm, &[pn]), app(el, w.hm, &[pab]));
    let res = app(el, v.lt, &[hn, hab]);
    let a1 = var(el, 1);
    let e0 = app(el, v.eq, &[a1, v.lit0]);
    let ne0 = v.no(el, e0);
    let body = pi(el, "H", ne0, res);
    let ty = pi_nat2(el, v, body);
    let p2 = typed(el, r.pf, ty)?;
    Ok(vec![p1, p2])
}

/// The arguments of `gcd_eqs` after `G`.
fn gcd_args<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>) -> R<Vec<E>> {
    let um = fuel(el, "Nat.mod")?;
    let mut args = fuel_args(el, v, &um, true)?;
    let mut rest: Vec<Ex<'t>> = v.nateq().to_vec();
    rest.extend([v.bp, v.bd]);
    rest.extend(&fix_args(v, &r.w)[4..]);
    rest.extend([r.f, r.pack, r.w.f_lam, r.pf]);
    for a in rest {
        args.push(el.tr(a)?);
    }
    Ok(args)
}

fn gcd_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>, targs: &[E]) -> R<P> {
    let w = &r.w;
    let mut hyps = vec![fact(el, "Nat.mod")?, cond_dec(el, v, true)?, bool_dec(el, v)?, fix_eqs(el, v, w)?];
    hyps.extend(closed_all(el, &[r.f, r.pack, w.f_lam, r.pf])?);
    hyps.push(typing(el, "Nat.gcd")?);
    let fty = w.fty(el, v);
    hyps.push(typed(el, w.f_lam, fty)?);
    let fm = konst(el, "Nat.mod", &[])?;
    hyps.extend(rec_typings(el, v, r, |el, a, b| {
        let m = app(el, fm, &[b, a]);
        Ok((m, a))
    })?);
    hyps.push(eqn(el, |el| {
        let (m, n) = (open(el, "m", v.nat)?, open(el, "n", v.nat)?);
        let lhs = app(el, r.f, &[m, n]);
        let a = app(el, r.pack, &[m, n]);
        Ok((lhs, app(el, w.fix, &[w.al, w.motive, w.hm, w.f_lam, a])))
    })?);
    hyps.push(eqn_at(el, |el| {
        let (m, n) = (open(el, "m", v.nat)?, open(el, "n", v.nat)?);
        let a = app(el, r.pack, &[m, n]);
        Ok((app(el, w.hm, &[a]), m, Some(v.nat)))
    })?);
    hyps.push(eqn_at(el, |el| {
        let n = open(el, "n", v.nat)?;
        let a = app(el, r.pack, &[v.lit0, n]);
        let ihty = w.ih_ty(el, v, a);
        let ih = open(el, "ih", ihty)?;
        let ma = app(el, w.motive, &[a]);
        Ok((app(el, w.f_lam, &[a, ih]), n, Some(ma)))
    })?);
    hyps.push(eqn_at(el, |el| {
        let (m, n) = (open(el, "m", v.nat)?, open(el, "n", v.nat)?);
        let sm = v.s(el, m);
        let e0 = app(el, v.eq, &[sm, v.lit0]);
        let ne0 = v.no(el, e0);
        let hne = open(el, "H", ne0)?;
        let a = app(el, r.pack, &[sm, n]);
        let ihty = w.ih_ty(el, v, a);
        let ih = open(el, "ih", ihty)?;
        let lhs = app(el, w.f_lam, &[a, ih]);
        let fm = konst(el, "Nat.mod", &[])?;
        let nm = app(el, fm, &[n, sm]);
        let a2 = app(el, r.pack, &[nm, sm]);
        let pf = app(el, r.pf, &[sm, n, hne]);
        let ma = app(el, w.motive, &[a]);
        Ok((lhs, app(el, ih, &[a2, pf]), Some(ma)))
    })?);
    mm(el.g.env.thm_n("gcd_eqs_i", targs, &hyps))
}

/// The arguments of `bitwise_eqs` after `G`.
fn bitwise_args<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>) -> R<Vec<E>> {
    let (ud, um) = (fuel(el, "Nat.div")?, fuel(el, "Nat.mod")?);
    let mut args = Vec::new();
    for a in v.d().iter().chain(&v.natle()) {
        args.push(el.tr(*a)?);
    }
    args.extend(natlit::rel_args(el, natlit::eqs("Nat.sub").unwrap()).ok_or("no `Nat.sub`")?);
    let mut rest = vec![ud.f, ud.go, um.f, um.go, ud.pfs, ud.lem, v.ite];
    rest.extend(v.nateq());
    rest.extend([v.bp, v.bd, konst(el, "Nat.add", &[])?]);
    rest.extend(&fix_args(v, &r.w)[4..]);
    rest.extend([r.f, r.pack, r.w.f_lam, r.pf, v.decide]);
    for a in rest {
        args.push(el.tr(a)?);
    }
    Ok(args)
}

fn bitwise_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>, targs: &[E]) -> R<P> {
    let w = &r.w;
    let mut hyps = vec![fact(el, "Nat.div")?, fact(el, "Nat.mod")?, cond_dec(el, v, true)?, bool_dec(el, v)?, fact(el, "Nat.add")?, fix_eqs(el, v, w)?];
    hyps.extend(closed_all(el, &[r.f, r.pack, w.f_lam, r.pf, v.decide])?);
    hyps.push(typing(el, "Nat.bitwise")?);
    {
        let fty = w.fty(el, v);
        let bbb = bool_fn(el, v);
        let ty = pi(el, "bf", bbb, fty);
        hyps.push(typed(el, w.f_lam, ty)?);
    }
    let fd = konst(el, "Nat.div", &[])?;
    hyps.extend(rec_typings(el, v, r, |el, a, b| {
        let (a2, b2) = (app(el, fd, &[a, v.lit2]), app(el, fd, &[b, v.lit2]));
        Ok((a2, b2))
    })?);
    let bbb = bool_fn(el, v);
    hyps.push(eqn(el, |el| {
        let (f, n, m) = (open(el, "f", bbb)?, open(el, "n", v.nat)?, open(el, "m", v.nat)?);
        let lhs = app(el, r.f, &[f, n, m]);
        let (ff, a) = (app(el, w.f_lam, &[f]), app(el, r.pack, &[n, m]));
        Ok((lhs, app(el, w.fix, &[w.al, w.motive, w.hm, ff, a])))
    })?);
    hyps.push(eqn_at(el, |el| {
        let (n, m) = (open(el, "n", v.nat)?, open(el, "m", v.nat)?);
        let a = app(el, r.pack, &[n, m]);
        Ok((app(el, w.hm, &[a]), n, Some(v.nat)))
    })?);
    hyps.push(eqn(el, |el| {
        let (p, b) = (open(el, "p", v.prop)?, open(el, "b", v.bool_)?);
        let tpb = v.t(el, p, b);
        let h = open(el, "H", tpb)?;
        let rr = v.r(el, p, b, h);
        Ok((app(el, v.decide, &[p, rr]), b))
    })?);
    hyps.push(eqn_at(el, |el| {
        let (f, n, m) = (open(el, "f", bbb)?, open(el, "n", v.nat)?, open(el, "m", v.nat)?);
        let a = app(el, r.pack, &[n, m]);
        let ihty = w.ih_ty(el, v, a);
        let ih = open(el, "ih", ihty)?;
        let ff = app(el, w.f_lam, &[f]);
        let lhs = app(el, ff, &[a, ih]);
        let (fd, fm, fa) = (konst(el, "Nat.div", &[])?, konst(el, "Nat.mod", &[])?, konst(el, "Nat.add", &[])?);
        // `dite (bp (f b1 b2)) (bd (f b1 b2)) (λ _. a) (λ _. b)`
        let sel = |el: &mut El<'_, '_, 't, '_>, b1: Ex<'t>, b2: Ex<'t>, a: Ex<'t>, b: Ex<'t>| {
            let fb = app(el, f, &[b1, b2]);
            let (p, d) = (app(el, v.bp, &[fb]), app(el, v.bd, &[fb]));
            v.dite_const(el, p, d, a, b)
        };
        // `dec (eq (fm x 2) 1) (deq (fm x 2) 1)`: the low bit of `x`
        let bit = |el: &mut El<'_, '_, 't, '_>, x: Ex<'t>| {
            let x2 = app(el, fm, &[x, v.lit2]);
            let (p, d) = (app(el, v.eq, &[x2, v.lit1]), app(el, v.deq, &[x2, v.lit1]));
            app(el, v.decide, &[p, d])
        };
        let (en, em) = (app(el, v.eq, &[n, v.lit0]), app(el, v.eq, &[m, v.lit0]));
        let (dn, dm) = (app(el, v.deq, &[n, v.lit0]), app(el, v.deq, &[m, v.lit0]));
        // n = 0
        let a_branch = {
            let s = sel(el, v.ff, v.tt, m, v.lit0);
            lam(el, "h", en, s)
        };
        // n ≠ 0 (`h`, the proof the recursive call takes), m = 0
        let b1 = {
            let s = sel(el, v.tt, v.ff, n, v.lit0);
            lam(el, "h", em, s)
        };
        // n ≠ 0, m ≠ 0: the recursive call `r` is under three binders (`h`, `h1` and the
        // branch's), so `h` is `# 2` there
        let b2 = {
            let (bn, bm) = (bit(el, n), bit(el, m));
            let h = var(el, 2);
            let (n2, m2) = (app(el, fd, &[n, v.lit2]), app(el, fd, &[m, v.lit2]));
            let a2 = app(el, r.pack, &[n2, m2]);
            let pf = app(el, r.pf, &[n, m, h]);
            let rc = app(el, ih, &[a2, pf]);
            let rr = app(el, fa, &[rc, rc]);
            let odd = app(el, fa, &[rr, v.lit1]);
            let s = sel(el, bn, bm, odd, rr);
            let nem = v.no(el, em);
            lam(el, "h1", nem, s)
        };
        let inner = app(el, v.dite, &[em, dm, b1, b2]);
        let nen = v.no(el, en);
        let b_branch = lam(el, "h", nen, inner);
        let ma = app(el, w.motive, &[a]);
        Ok((lhs, app(el, v.dite, &[en, dn, a_branch, b_branch]), Some(ma)))
    })?);
    mm(el.g.env.thm_n("bitwise_eqs_i", targs, &hyps))
}

/// The Bool function of `Nat.land` etc. (`Nat.bitwise bf`), with its truth table as the
/// spec's `r1 r2 r3 r4` (`bf t t`, `bf t u`, `bf u t`, `bf u u`).
fn bitop<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, lean: &str) -> R<(Ex<'t>, [Ex<'t>; 4])> {
    let val = value(el, lean)?;
    let (head, args) = el.tc.ctx.unfold_apps(val);
    let bitwise = name(el, "Nat.bitwise")?;
    if !matches!(el.tc.ctx.read_expr(head), Expr::Const { name, .. } if name == bitwise) || args.len() != 1 {
        return Err(format!("`{lean}` is not `Nat.bitwise f`"))
    }
    let (t, u) = (v.tt, v.ff);
    let table = match lean {
        "Nat.land" => [t, u, u, u],
        "Nat.lor" => [t, t, t, u],
        "Nat.xor" => [u, t, t, u],
        _ => return Err(format!("internal: no truth table for `{lean}`")),
    };
    Ok((args[0], table))
}

fn bitop_args<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>, lean: &str) -> R<Vec<E>> {
    let mut args = bitwise_args(el, v, r)?;
    let (bf, table) = bitop(el, v, lean)?;
    let f = konst(el, lean, &[])?;
    for a in [f, bf].into_iter().chain(table) {
        args.push(el.tr(a)?);
    }
    Ok(args)
}

fn bitop_eqs<'t>(el: &mut El<'_, '_, 't, '_>, v: &Voc<'t>, r: &Rec<'t>, lean: &str, targs: &[E]) -> R<P> {
    let (bf, table) = bitop(el, v, lean)?;
    let f = konst(el, lean, &[])?;
    let mut hyps = vec![fact(el, "Nat.bitwise")?];
    hyps.extend(closed_all(el, &[f, bf])?);
    hyps.push(typing(el, lean)?);
    let bbb = bool_fn(el, v);
    hyps.push(typed(el, bf, bbb)?);
    let fb = app(el, r.f, &[bf]);
    hyps.push(el.defeq(f, fb)?);
    for (i, (a, b)) in [(v.tt, v.tt), (v.tt, v.ff), (v.ff, v.tt), (v.ff, v.ff)].into_iter().enumerate() {
        let x = app(el, bf, &[a, b]);
        hyps.push(el.defeq(x, table[i])?);
    }
    mm(el.g.env.thm_n("bitop_eqs_i", targs, &hyps))
}

// ------------------------------------------------------------------ the theorems

/// The arguments of `o`'s relation after `G` (as the `_eqs` theorem and the `_lit` rules
/// take them). Statements must not depend on proving, so this only builds terms.
pub fn rel_args(el: &mut El<'_, '_, '_, '_>, o: &Op) -> R<Vec<E>> {
    let v = Voc::new(el)?;
    match o.lean {
        "Nat.div" | "Nat.mod" => {
            let u = fuel(el, o.lean)?;
            fuel_args(el, &v, &u, o.lean == "Nat.mod")
        }
        "Nat.gcd" => {
            let r = rec_parts(el, &v, o.lean)?;
            gcd_args(el, &v, &r)
        }
        "Nat.bitwise" => {
            let r = rec_parts(el, &v, o.lean)?;
            bitwise_args(el, &v, &r)
        }
        _ => {
            let r = rec_parts(el, &v, "Nat.bitwise")?;
            bitop_args(el, &v, &r, o.lean)
        }
    }
}

/// The arguments of `o`'s `_lit` rules between `G` and the numerals: the relation's, but
/// the rules `nat_land_lit` etc. fix the truth table `r1 r2 r3 r4` of `bitop_eqs`.
pub fn lit_rule_args(el: &mut El<'_, '_, '_, '_>, o: &Op) -> R<Vec<E>> {
    let mut args = rel_args(el, o)?;
    if o.rel == "bitop_eqs" {
        args.truncate(args.len() - 4);
    }
    Ok(args)
}

/// Derive `o`'s relation for the environment's definition (`cname`) and state it as the
/// theorem `{cname}_eqs`. The definition is in the type checker's environment (the driver
/// extends it, `gen::run`); the dependencies' `_eqs` theorems must exist.
pub fn eqs_theorem(el: &mut El<'_, '_, '_, '_>, o: &Op, cname: &str) -> R<ThId> {
    for dep in o.deps {
        if !el.g.nat_eqs.contains_key(*dep) {
            return Err(format!("the equations of `{dep}` were not derived"))
        }
    }
    let args = rel_args(el, o)?;
    let g = &mut *el.g;
    let gv = g.env.var(0);
    let mut targs = vec![gv];
    targs.extend(&args);
    let concl = g.env.app_n(o.rel, &targs);
    let name = g.thms.fresh(&format!("{cname}_eqs"));
    let doc = format!("`{}` has the defining equations of the spec's `{}` (Lean4Lean's `Primitive.lean`).", o.lean, o.rel);
    let args_g = g.g_args(&[]);
    if g.replay {
        return add_thm(&mut g.env, &name, args_g, vec![], concl, false, false, None, &doc)
    }
    if el.depth() != 0 {
        return Err("internal: the equations are derived at the top level".into())
    }
    // the equations are about the definitions, not the kernel's computation on literals
    el.tc.nat_ops_off = true;
    let r = derive(el, o, &targs);
    el.tc.nat_ops_off = false;
    let p = r?;
    add_thm(&mut el.g.env, &name, args_g, vec![], concl, false, false, Some(p), &doc)
}

fn derive(el: &mut El<'_, '_, '_, '_>, o: &Op, targs: &[E]) -> R<P> {
    let v = Voc::new(el)?;
    match o.lean {
        "Nat.div" | "Nat.mod" => {
            let u = fuel(el, o.lean)?;
            fuel_eqs(el, &v, &u, o.lean, targs)
        }
        "Nat.gcd" => {
            let r = rec_parts(el, &v, o.lean)?;
            gcd_eqs(el, &v, &r, targs)
        }
        "Nat.bitwise" => {
            let r = rec_parts(el, &v, o.lean)?;
            bitwise_eqs(el, &v, &r, targs)
        }
        _ => {
            let r = rec_parts(el, &v, "Nat.bitwise")?;
            bitop_eqs(el, &v, &r, o.lean, targs)
        }
    }
}
