//! The elaborator: typed LeanTT derivations (as `lean.mm0` proofs) for nanoda terms.
//!
//! Terms stay nanoda expressions (locally nameless, with de Bruijn-level fvars) while the
//! elaborator works. The open fvars form the context, and terms are translated to MM0
//! de Bruijn terms when a proof needs them.
//!
//! Every term `x` gets a canonical type `τ(x)`, computed the way nanoda's `infer` does,
//! together with a derivation of `Γ ⊢ x : τ(x)`. Every defeq derivation `Γ ⊢ x ≡ y : τ(x)`
//! follows the rule the tracer recorded for `(x, y)`. When two types meet that are only
//! defeq (an argument type and a binder type, or the canonical types of a term and its
//! reduct), the elaborator asks nanoda again and inserts `defeqDF`. Reducts are re-typed
//! from scratch (the simple fallback), not through typing handles.
//!
//! A derivation about closed terms does not depend on the context. Under binders, the
//! elaborator makes it at depth 0 (over the statement's variable `G`), and uses it as a local
//! lemma over `G` and the level variables, instantiated at the current context.
//!
//! A β-step's reduct is a substitution instance, and so is the lambda body the next β-step
//! must type. Such terms get a typing handle: their typing comes from the typing of the term
//! before substitution, by the spec's `instDF`, instead of being derived again.

use crate::gen::{ConstKind, Gen};
use crate::natlit;
use nanoda_lib::trace::DefEqWhy;
use nanoda_lib::expr::{Expr, FVarId};
use nanoda_lib::level::Level;
use nanoda_lib::tc::TypeChecker;
use nanoda_lib::util::{ExprPtr, LevelPtr, NamePtr};
use mm0kit::bin::Rel;
use mm0kit::env::{ThId, E, P};
use num_bigint::BigUint;
use rustc_hash::FxHashMap as HashMap;

pub type R<A> = Result<A, String>;

/// An `mm0kit` result as an elaborator result.
pub(crate) fn mm<A>(r: mm0kit::env::Result<A>) -> R<A> { r.map_err(|e| e.0) }

const MAX_REDUCE_STEPS: usize = 100_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    Beta,
    Zeta,
    Delta,
    SortSimp,
    /// Projection of a structure that reduces to a constructor application.
    Proj,
    /// `Quot.lift`/`Quot.ind` of a `Quot.mk`.
    Quot,
    /// A recursor applied to a constructor application (after K or structure eta, if any).
    Iota,
    /// `Nat.succ` or an accelerated operation applied to literals (nanoda's `try_reduce_nat`).
    Nat,
}

/// A typing handle: the term is `src` with `arg` substituted for the fvar `src_locals[base]`.
/// `src` lives under the fvars `src_locals`; the term lives under `src_locals[..base]` (where
/// `arg` lives too) followed by fvars for the remaining entries, with `arg` substituted in
/// their types.
#[derive(Clone)]
struct Handle<'t> {
    src: ExprPtr<'t>,
    src_locals: Vec<ExprPtr<'t>>,
    base: usize,
    arg: ExprPtr<'t>,
}

pub struct Elab<'a, 'x, 't, 'p> {
    pub tc: &'a mut TypeChecker<'x, 't, 'p>,
    pub g: &'a mut Gen,
    uparams: Vec<NamePtr<'t>>,
    locals: Vec<ExprPtr<'t>>,
    /// `ctxs[d]` is the MM0 context made of the first `d` open fvars, over the variable `G`.
    ctxs: Vec<E>,
    tr_memo: HashMap<(ExprPtr<'t>, usize), E>,
    lvl_memo: HashMap<LevelPtr<'t>, E>,
    infer_memo: HashMap<(ExprPtr<'t>, E), (ExprPtr<'t>, P)>,
    defeq_memo: HashMap<(ExprPtr<'t>, ExprPtr<'t>, E), P>,
    /// Statistics: how often our canonical type differed from nanoda's inferred type.
    pub type_mismatches: usize,
    /// Nesting of `defeq` calls, to report runaway recursion instead of overflowing the stack.
    nest: usize,
    trace: bool,
    /// `LEAN0_PROFILE`: report each `defeq` that adds at least this many proof nodes.
    profile: Option<usize>,
    /// Give up on the declaration once the proof arena reaches this size (see `MAX_PROOF_NODES`).
    pf_limit: usize,
    /// Local lemmas for closed derivations, by their proof at depth 0 (`None`: too small to be
    /// worth one, and re-derived where it is needed).
    closed_lemmas: HashMap<P, Option<ThId>>,
    /// The lemmas' name prefix and arguments (`G` and the level variables).
    lemma_name: String,
    lemma_args: mm0kit::env::Args,
    /// Typing handles, by term and context.
    handles: HashMap<(ExprPtr<'t>, E), Handle<'t>>,
    /// The lowest fvar level in a term (`u16::MAX` if none) and one plus the highest (0 if
    /// none), see `suffix_base` and `prefix_top`.
    fvar_range_memo: HashMap<ExprPtr<'t>, (u16, u16)>,
}

/// Proof nodes one declaration may add (overridden by `LEAN0_MAX_PROOF_NODES`). A few
/// declarations need far more memory than nanoda does; this makes them fail instead of
/// exhausting it.
const MAX_PROOF_NODES: usize = 25_000_000;

/// A closed derivation with at most this many proof steps is re-derived in each context instead
/// of becoming a lemma: using a lemma costs a step and a statement too.
const MIN_LEMMA_STEPS: usize = 4;

impl<'a, 'x, 't: 'x, 'p: 't> Elab<'a, 'x, 't, 'p> {
    /// `lemma_name` prefixes the names of local lemmas, whose arguments are `lemma_args`: `G`
    /// and the level variables, as in the declaration's statements.
    pub fn new(
        tc: &'a mut TypeChecker<'x, 't, 'p>, g: &'a mut Gen, uparams: Vec<NamePtr<'t>>, lemma_name: String,
        lemma_args: Vec<(String, u8)>,
    ) -> Self {
        tc.enable_trace();
        let gvar = g.env.var(0);
        let budget = std::env::var("LEAN0_MAX_PROOF_NODES").ok().and_then(|s| s.parse().ok()).unwrap_or(MAX_PROOF_NODES);
        let pf_limit = g.env.num_pfs() + budget;
        Elab {
            tc,
            g,
            uparams,
            locals: Vec::new(),
            ctxs: vec![gvar],
            tr_memo: HashMap::default(),
            lvl_memo: HashMap::default(),
            infer_memo: HashMap::default(),
            defeq_memo: HashMap::default(),
            type_mismatches: 0,
            nest: 0,
            trace: std::env::var_os("LEAN0_TRACE").is_some(),
            profile: std::env::var("LEAN0_PROFILE").ok().and_then(|v| v.parse().ok()),
            pf_limit,
            closed_lemmas: HashMap::default(),
            lemma_name,
            lemma_args: lemma_args.into(),
            handles: HashMap::default(),
            fvar_range_memo: HashMap::default(),
        }
    }

    fn d(&self) -> usize { self.locals.len() }

    /// Run `f` as the cost centre `name` (`LEAN0_COSTS`).
    fn cc<A>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> R<A>) -> R<A> {
        if self.g.costs.is_none() {
            return f(self)
        }
        self.g.cost_enter(name);
        let r = f(self);
        self.g.cost_exit();
        r
    }

    pub fn depth(&self) -> usize { self.locals.len() }

    /// Instantiate the loose bound variables of `e` with the open fvars.
    pub fn inst_locals(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let locals = self.locals.clone();
        self.tc.ctx.inst(e, &locals)
    }

    /// The constants occurring in `e`.
    pub fn const_names(&self, e: ExprPtr<'t>, out: &mut Vec<NamePtr<'t>>) {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue
            }
            match self.read(e) {
                Expr::Const { name, .. } => out.push(name),
                Expr::App { fun, arg, .. } => stack.extend([fun, arg]),
                Expr::Lambda { binder_type, body, .. } | Expr::Pi { binder_type, body, .. } => stack.extend([binder_type, body]),
                Expr::Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
                Expr::Proj { structure, .. } => stack.push(structure),
                Expr::Local { binder_type, .. } => stack.push(binder_type),
                _ => {}
            }
        }
    }

    pub fn open_pub(&mut self, name: NamePtr<'t>, style: nanoda_lib::expr::BinderStyle, ty: ExprPtr<'t>) -> R<ExprPtr<'t>> { self.open(name, style, ty) }

    pub fn close_pub(&mut self) { self.close() }

    /// The `i`th open fvar (from the outermost).
    pub fn local(&self, i: usize) -> Option<ExprPtr<'t>> { self.locals.get(i).copied() }

    fn ctx(&self) -> E { self.ctxs[self.d()] }

    /// The MM0 context of the open binders, over `G`.
    pub fn ctx_pub(&self) -> E { self.ctx() }

    /// Forget every memoized proof (after the generator rolled proofs back).
    pub fn forget_proofs(&mut self) {
        self.infer_memo.clear();
        self.defeq_memo.clear();
        self.closed_lemmas.clear();
        self.handles.clear();
    }

    fn read(&self, e: ExprPtr<'t>) -> Expr<'t> { self.tc.ctx.read_expr(e) }

    pub fn show(&mut self, e: ExprPtr<'t>) -> String {
        match self.tr(e) {
            Ok(m) => self.g.show(m),
            Err(_) => format!("{:?}", self.tc.ctx.debug_print(e)),
        }
    }

    // ------------------------------------------------------------------ translation

    pub fn trl(&mut self, l: LevelPtr<'t>) -> R<E> {
        if let Some(&r) = self.lvl_memo.get(&l) {
            return Ok(r)
        }
        let env = &mut self.g.env;
        let r = match self.tc.ctx.read_level(l) {
            Level::Zero => env.app_n("lz", &[]),
            Level::Succ(a, _) => {
                let a = self.trl(a)?;
                self.g.env.app_n("ls", &[a])
            }
            Level::Max(a, b, _) => {
                let (a, b) = (self.trl(a)?, self.trl(b)?);
                self.g.env.app_n("lmax", &[a, b])
            }
            Level::IMax(a, b, _) => {
                let (a, b) = (self.trl(a)?, self.trl(b)?);
                self.g.env.app_n("limax", &[a, b])
            }
            Level::Param(n, _) => match self.uparams.iter().position(|&u| u == n) {
                Some(i) => self.g.env.var(1 + i as u16),
                None => return Err(format!("undeclared universe parameter {:?}", self.tc.ctx.debug_print(n))),
            },
        };
        self.lvl_memo.insert(l, r);
        Ok(r)
    }

    /// Translate at the current depth.
    pub fn tr(&mut self, e: ExprPtr<'t>) -> R<E> {
        let d = self.d();
        self.tr_at(e, d)
    }

    /// Translate `e` as a term under `d` binders: the open fvars plus binders of `e` itself.
    pub fn tr_at(&mut self, e: ExprPtr<'t>, d: usize) -> R<E> {
        let key = (e, if self.tc.ctx.has_fvars(e) { d } else { usize::MAX });
        if let Some(&r) = self.tr_memo.get(&key) {
            return Ok(r)
        }
        let r = match self.read(e) {
            Expr::Var { dbj_idx, .. } => self.g.lean.bvar(&mut self.g.env, dbj_idx as usize),
            Expr::Local { id: FVarId::DbjLevel(k), .. } => {
                let k = k as usize;
                if k >= d {
                    return Err("fvar out of scope".into())
                }
                self.g.lean.bvar(&mut self.g.env, d - 1 - k)
            }
            Expr::Local { .. } => return Err("unique fvar in a term".into()),
            Expr::Sort { level, .. } => {
                let l = self.trl(level)?;
                self.g.lean.srt(&mut self.g.env, l)
            }
            Expr::Const { name, levels, .. } => {
                let s = self.g.lean_name(self.tc, name);
                let Some(ci) = self.g.consts.get(&s) else { return Err(format!("unknown constant {s}")) };
                if ci.nlevels != self.tc.ctx.read_levels(levels).len() {
                    return Err(format!("wrong number of universe levels for {s}"))
                }
                let ls: Vec<LevelPtr<'t>> = self.tc.ctx.read_levels(levels).to_vec();
                let ls: Vec<E> = ls.into_iter().map(|l| self.trl(l)).collect::<R<_>>()?;
                self.g.const_term(&s, &ls).ok_or_else(|| format!("no term for {s}"))?
            }
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.tr_at(fun, d)?, self.tr_at(arg, d)?);
                self.g.lean.app(&mut self.g.env, f, a)
            }
            Expr::Lambda { binder_type, body, .. } => {
                let (a, b) = (self.tr_at(binder_type, d)?, self.tr_at(body, d + 1)?);
                self.g.lean.lam(&mut self.g.env, a, b)
            }
            Expr::Pi { binder_type, body, .. } => {
                let (a, b) = (self.tr_at(binder_type, d)?, self.tr_at(body, d + 1)?);
                self.g.lean.pi(&mut self.g.env, a, b)
            }
            // `let` is inlined
            Expr::Let { val, body, .. } => {
                let (v, b) = (self.tr_at(val, d)?, self.tr_at(body, d + 1)?);
                self.g.lean.inst_pure(&mut self.g.env, 0, b, v)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let s = self.g.lean_name(self.tc, ty_name);
                let Some(si) = self.g.structs.get(&s) else { return Err(format!("projection of unknown structure {s}")) };
                let b = self.g.env.app(si.blk, &[]);
                let x = self.tr_at(structure, d)?;
                self.g.lean.proj(&mut self.g.env, b, idx, x)
            }
            Expr::NatLit { ptr, .. } => {
                let n = self.tc.ctx.read_bignum(ptr).unwrap().clone();
                self.g.bins.lit(&mut self.g.env, &n)
            }
            // a string literal means its expansion `String.ofList [Char.ofNat n, ...]`
            Expr::StringLit { .. } => {
                let x = self.str_expand(e)?;
                self.tr_at(x, d)?
            }
        };
        self.tr_memo.insert(key, r);
        Ok(r)
    }

    // ------------------------------------------------------------------ binders

    fn open(&mut self, name: NamePtr<'t>, style: nanoda_lib::expr::BinderStyle, ty: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        let t = self.tr(ty)?;
        let g = self.ctx();
        let x = self.tc.ctx.mk_dbj_level(name, style, ty);
        assert_eq!(self.tc.ctx.dbj_level_counter as usize, self.d() + 1, "fvar counter out of sync");
        self.locals.push(x);
        let c = self.g.lean.cons(&mut self.g.env, t, g);
        self.ctxs.push(c);
        Ok(x)
    }

    fn close(&mut self) {
        let x = self.locals.pop().unwrap();
        self.ctxs.pop();
        self.tc.ctx.replace_dbj_level(x);
    }

    /// Run `f` at depth 0, with no fvars open: for derivations about closed terms.
    fn at_top<A>(&mut self, f: impl FnOnce(&mut Self) -> R<A>) -> R<A> { self.with_locals(&[], f) }

    /// Run `f` with exactly the fvars `locals` open (each typed under the ones before it).
    /// nanoda's fvars are de Bruijn levels, so those `f` opens are numbered from there; a
    /// term's meaning does not depend on the context it was made in, so caches stay valid.
    fn with_locals<A>(&mut self, locals: &[ExprPtr<'t>], f: impl FnOnce(&mut Self) -> R<A>) -> R<A> {
        let saved = std::mem::take(&mut self.locals);
        let top = vec![self.ctxs[0]];
        let ctxs = std::mem::replace(&mut self.ctxs, top);
        let counter = std::mem::replace(&mut self.tc.ctx.dbj_level_counter, 0);
        let r = (|| {
            for &x in locals {
                let Expr::Local { binder_type, .. } = self.read(x) else { unreachable!() };
                let (t, g) = (self.tr(binder_type)?, self.ctx());
                let c = self.g.lean.cons(&mut self.g.env, t, g);
                self.locals.push(x);
                self.ctxs.push(c);
                self.tc.ctx.dbj_level_counter += 1;
            }
            f(self)
        })();
        self.locals = saved;
        self.ctxs = ctxs;
        self.tc.ctx.dbj_level_counter = counter;
        r
    }

    /// The lowest fvar level in `e` (`u16::MAX` if it has none) and one plus the highest (0).
    fn fvar_range(&mut self, e: ExprPtr<'t>) -> (u16, u16) {
        if !self.tc.ctx.has_fvars(e) {
            return (u16::MAX, 0)
        }
        if let Some(&m) = self.fvar_range_memo.get(&e) {
            return m
        }
        let join = |el: &mut Self, es: &[ExprPtr<'t>]| {
            es.iter().fold((u16::MAX, 0), |(a, b), &e| {
                let (c, d) = el.fvar_range(e);
                (a.min(c), b.max(d))
            })
        };
        let m = match self.read(e) {
            Expr::Local { id: nanoda_lib::expr::FVarId::DbjLevel(l), .. } => (l, l + 1),
            Expr::App { fun, arg, .. } => join(self, &[fun, arg]),
            Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => join(self, &[binder_type, body]),
            Expr::Let { binder_type, val, body, .. } => join(self, &[binder_type, val, body]),
            Expr::Proj { structure, .. } => self.fvar_range(structure),
            _ => (u16::MAX, 0),
        };
        self.fvar_range_memo.insert(e, m);
        m
    }

    fn fvar_min(&mut self, e: ExprPtr<'t>) -> u16 { self.fvar_range(e).0 }

    /// The length of the shortest prefix of the context that `es` live in, if that is shorter
    /// than the context (and `es` mention fvars at all; closed terms go to `at_top`). A
    /// derivation about `es` can then be made there (`with_prefix`) and weakened (`weaken`),
    /// so that it is shared by every context with that prefix.
    fn prefix_top(&mut self, es: &[ExprPtr<'t>]) -> Option<usize> {
        let t = es.iter().map(|&e| self.fvar_range(e).1 as usize).max().unwrap_or(0);
        (0 < t && t < self.d()).then_some(t)
    }

    /// Run `f` with only the first `t` open fvars open.
    fn with_prefix<A>(&mut self, t: usize, f: impl FnOnce(&mut Self) -> R<A>) -> R<A> {
        let locals = self.locals.split_off(t);
        let ctxs = self.ctxs.split_off(t + 1);
        let counter = std::mem::replace(&mut self.tc.ctx.dbj_level_counter, t as u16);
        let r = f(self);
        self.locals.extend(locals);
        self.ctxs.extend(ctxs);
        self.tc.ctx.dbj_level_counter = counter;
        r
    }

    /// `weakDF`: move `p`, made under the first `t` open fvars, into the current context.
    fn weaken(&mut self, p: P, t: usize) -> R<P> {
        let (n, g) = (self.d() - t, self.ctx());
        mm(self.g.lean.weak_df(&mut self.g.env, n, g, p))
    }

    /// The least `b` such that `es` and the types of the open fvars from `b` on mention only
    /// fvars from `b` on. A derivation about `es` then depends only on the context's last
    /// `d - b` entries, so it can be made once, schematic in the rest (`with_suffix`).
    fn suffix_base(&mut self, es: &[ExprPtr<'t>]) -> usize {
        let d = self.d();
        let mut b = es.iter().map(|&e| self.fvar_min(e) as usize).min().unwrap_or(d).min(d);
        let mut j = b;
        while j < d {
            let Expr::Local { binder_type, .. } = self.read(self.locals[j]) else { unreachable!() };
            let m = self.fvar_min(binder_type) as usize;
            if m < b {
                (b, j) = (m, m);
            } else {
                j += 1;
            }
        }
        b
    }

    /// Run `f` on `es` moved into a context of only the open fvars from `base` on (renumbered
    /// from level 0, under the variable `G`), and return `f`'s terms moved back. `base` must be
    /// `suffix_base(es)` or more, so the MM0 translations agree: they are de Bruijn terms.
    fn with_suffix<A>(
        &mut self, base: usize, es: &[ExprPtr<'t>], f: impl FnOnce(&mut Self, &[ExprPtr<'t>]) -> R<(Vec<ExprPtr<'t>>, A)>,
    ) -> R<(Vec<ExprPtr<'t>>, A)> {
        let d = self.d();
        let outer: Vec<ExprPtr<'t>> = self.locals[base..].to_vec();
        let abs: Vec<ExprPtr<'t>> = es.iter().map(|&e| self.tc.ctx.abstr_levels(e, base as u16)).collect();
        let tys: Vec<(NamePtr<'t>, nanoda_lib::expr::BinderStyle, ExprPtr<'t>)> = outer
            .iter()
            .map(|&x| {
                let Expr::Local { binder_name, binder_style, binder_type, .. } = self.read(x) else { unreachable!() };
                (binder_name, binder_style, self.tc.ctx.abstr_levels(binder_type, base as u16))
            })
            .collect();
        let (rs, a) = self.with_locals(&[], |el| {
            // the new fvars, with the outer ones standing in for those not opened yet (unused)
            let mut subst = outer.clone();
            for (j, &(name, style, ty)) in tys.iter().enumerate() {
                let ty = el.tc.ctx.inst(ty, &subst);
                subst[j] = el.open(name, style, ty)?;
            }
            let moved: Vec<ExprPtr<'t>> = abs.iter().map(|&e| el.tc.ctx.inst(e, &subst)).collect();
            let r = f(el, &moved).map(|(rs, a)| (rs.iter().map(|&r| el.tc.ctx.abstr_levels(r, 0)).collect::<Vec<_>>(), a));
            for _ in 0..tys.len() {
                el.close();
            }
            r
        })?;
        debug_assert_eq!(self.d(), d);
        Ok((rs.iter().map(|&r| self.tc.ctx.inst(r, &outer)).collect(), a))
    }

    /// `e` is a binder whose body was just opened as `body` (with the newest fvar). If `e` has a
    /// typing handle, give `body` one too: the source's body, opened in the source's context.
    fn body_handle(&mut self, e: ExprPtr<'t>, body: ExprPtr<'t>) -> R<()> {
        let d = self.d();
        let Some(h) = self.handles.get(&(e, self.ctxs[d - 1])).cloned() else { return Ok(()) };
        let (Expr::Lambda { binder_name, binder_style, binder_type, body: b0, .. }
        | Expr::Pi { binder_name, binder_style, binder_type, body: b0, .. }) = self.read(h.src)
        else {
            return Ok(())
        };
        let (src, src_locals) = self.with_locals(&h.src_locals, |el| {
            let y = el.open(binder_name, binder_style, binder_type)?;
            let src = el.tc.ctx.inst(b0, &[y]);
            let r = el.body_handle(h.src, src).map(|()| (src, el.locals.clone()));
            el.close();
            r
        })?;
        self.handles.insert((body, self.ctx()), Handle { src, src_locals, ..h });
        Ok(())
    }

    /// `τ(e)` and `Γ ⊢ e : τ(e)` by `instDF`, from the handle's source and argument, or `None`
    /// if the handle does not fit.
    fn infer_handle(&mut self, e: ExprPtr<'t>, h: &Handle<'t>) -> R<Option<(ExprPtr<'t>, P)>> {
        let (base, d) = (h.base, self.d());
        if h.src_locals.len() != d + 1 || self.locals[..base] != h.src_locals[..base] {
            return Ok(None)
        }
        // the source's term and type, abstracted over the fvars from the substituted one on
        let (src_abs, t_abs, p0) = self.with_locals(&h.src_locals, |el| {
            let (t0, p0) = el.infer(h.src)?;
            Ok((el.tc.ctx.abstr_levels(h.src, base as u16), el.tc.ctx.abstr_levels(t0, base as u16), p0))
        })?;
        let mut substs = vec![h.arg];
        substs.extend_from_slice(&self.locals[base..]);
        if self.tc.ctx.inst(src_abs, &substs) != e {
            return Ok(None)
        }
        let t = self.tc.ctx.inst(t_abs, &substs);
        let Expr::Local { binder_type, .. } = self.read(h.src_locals[base]) else { unreachable!() };
        let pa = self.with_locals(&h.src_locals[..base], |el| {
            let (at, pa) = el.infer(h.arg)?;
            el.cast(pa, at, binder_type)
        })?;
        let p = mm(self.g.lean.inst_df(&mut self.g.env, d - base, pa, p0))?;
        let want = self.deq(e, e, t)?;
        Ok((self.g.env.concl(p) == want).then_some((t, p)))
    }

    /// Use `p0: G ⊢ ...`, a derivation made by `at_top`, in the current context: as an instance
    /// of its local lemma, or `None` if it is to be re-derived here.
    fn closed_use(&mut self, p0: P) -> R<Option<P>> {
        let g = self.ctx();
        self.closed_use_at(p0, g)
    }

    /// `closed_use` for a derivation made by `with_suffix`: its `G` becomes `base`.
    fn closed_use_at(&mut self, p0: P, base: E) -> R<Option<P>> {
        let th = match self.closed_lemmas.get(&p0) {
            Some(&th) => th,
            None => {
                let th = if self.g.env.pf_size(p0, MIN_LEMMA_STEPS + 1) <= MIN_LEMMA_STEPS {
                    None
                } else {
                    // lemma names are outside the generated names' namespace (see `Names::fresh`)
                    let mut name = format!("{}{}_c{}", mm0kit::lean::FACT_PREFIX, self.lemma_name, self.closed_lemmas.len());
                    while self.g.env.has_thm(&name) {
                        name.push('_');
                    }
                    let args = self.lemma_args.clone();
                    Some(mm(self.g.env.add_lemma(&name, args, p0, crate::gen::split_budget()))?)
                };
                self.closed_lemmas.insert(p0, th);
                th
            }
        };
        let Some(th) = th else { return Ok(None) };
        let mut args = vec![base];
        args.extend((1..self.lemma_args.len()).map(|i| self.g.env.var(i as u16)));
        Ok(Some(mm(self.g.env.thm(th, &args, &[]))?))
    }

    // ------------------------------------------------------------------ helpers

    fn deq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, t: ExprPtr<'t>) -> R<E> {
        let (x, y, t) = (self.tr(x)?, self.tr(y)?, self.tr(t)?);
        let g = self.ctx();
        Ok(self.g.lean.deq(&mut self.g.env, g, x, y, t))
    }

    /// Check that `p` proves `Γ ⊢ x ≡ y : t` (catches translation and bookkeeping bugs early).
    fn check(&mut self, p: P, x: ExprPtr<'t>, y: ExprPtr<'t>, t: ExprPtr<'t>) -> R<()> {
        let want = self.deq(x, y, t)?;
        let have = self.g.env.concl(p);
        if want != have {
            return Err(format!("internal: derivation proves\n  {}\nbut expected\n  {}", self.g.show(have), self.g.show(want)))
        }
        Ok(())
    }

    /// Turn `p: Γ ⊢ x ≡ y : from` into `Γ ⊢ x ≡ y : to`.
    pub fn cast(&mut self, p: P, from: ExprPtr<'t>, to: ExprPtr<'t>) -> R<P> {
        if from == to || self.tr(from)? == self.tr(to)? {
            return Ok(p)
        }
        self.cc("cast", |el| {
            let q = el.defeq_ty(from, to)?;
            mm(el.g.lean.defeq_df(&mut el.g.env, q, p))
        })
    }

    /// Turn `p: Γ ⊢ x ≡ y : t` into a proof at `τ(x)`, as `defeq` returns: a rule may type `x`
    /// differently from `infer` (from its parts, in another context, or without a typing
    /// handle).
    fn at_type_of(&mut self, x: ExprPtr<'t>, p: P, t: ExprPtr<'t>) -> R<P> {
        self.cc("at_type_of", |el| {
            let tx = el.infer(x)?.0;
            el.cast(p, t, tx)
        })
    }

    /// `Γ ⊢ a ≡ b : Sort u`.
    fn defeq_ty(&mut self, a: ExprPtr<'t>, b: ExprPtr<'t>) -> R<P> {
        let q = self.defeq(a, b)?;
        let (ta, _) = self.infer(a)?;
        Ok(self.as_sort(q, ta)?.1)
    }

    /// Turn `p: Γ ⊢ x ≡ y : t` with `t` a type into one at `Sort u`, where `Sort u` is the weak
    /// head normal form of `t`. A literal sort is kept as it is: unlike nanoda's
    /// `infer_sort_of`, we do not simplify its level, since every rule accepts any sort and
    /// casting to the simplified sort would need a cast one universe up, and so on forever.
    pub fn as_sort(&mut self, p: P, t: ExprPtr<'t>) -> R<(LevelPtr<'t>, P)> {
        if let Expr::Sort { level, .. } = self.read(t) {
            return Ok((level, p))
        }
        let w = self.tc.whnf(t);
        let Expr::Sort { level, .. } = self.read(w) else { return Err(format!("not a sort: {}", self.show(t))) };
        Ok((level, self.cast(p, t, w)?))
    }

    fn as_pi(&mut self, p: P, t: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        if let Expr::Pi { .. } = self.read(t) {
            return Ok((t, p))
        }
        let w = self.tc.whnf(t);
        let Expr::Pi { .. } = self.read(w) else { return Err(format!("not a function type: {}", self.show(t))) };
        Ok((w, self.cast(p, t, w)?))
    }

    fn level_equiv(&mut self, a: LevelPtr<'t>, b: LevelPtr<'t>) -> R<P> {
        let (a, b) = (self.trl(a)?, self.trl(b)?);
        self.cc("level", |el| {
            let g = &mut *el.g;
            mm(g.lv.equiv(&g.lean, &mut g.env, a, b))
        })
    }

    // ------------------------------------------------------------------ typing

    /// `τ(e)` and a proof of `Γ ⊢ e : τ(e)` (as `deq Γ e e τ(e)`).
    pub fn infer(&mut self, e: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        let key = (e, self.ctx());
        if let Some(&r) = self.infer_memo.get(&key) {
            return Ok(r)
        }
        // A handle is used once: on success the memo has the result, and a failed one would fail
        // again. Removing it first also stops a cycle, since a reduct can contain its own
        // argument (`b[a]` for `b = x …`), and typing the argument meets the handle again.
        if let Some(h) = self.handles.remove(&key) {
            if let Some(r) = self.cc("infer.handle", |el| el.infer_handle(e, &h))? {
                self.infer_memo.insert(key, r);
                return Ok(r)
            }
        }
        if self.d() > 0 && !self.tc.ctx.has_fvars(e) {
            let (t, p0) = self.at_top(|el| el.infer(e))?;
            if let Some(p) = self.cc("infer.closed_use", |el| el.closed_use(p0))? {
                self.infer_memo.insert(key, (t, p));
                return Ok((t, p))
            }
        } else if let Some(top) = self.prefix_top(&[e]) {
            let (t, p0) = self.with_prefix(top, |el| el.infer(e))?;
            let p = self.cc("infer.weaken", |el| el.weaken(p0, top))?;
            self.check(p, e, e, t)?;
            self.infer_memo.insert(key, (t, p));
            return Ok((t, p))
        } else if let b @ 1.. = self.suffix_base(&[e]) {
            let (ts, p0) = self.with_suffix(b, &[e], |el, es| {
                let (t, p) = el.infer(es[0])?;
                Ok((vec![t], p))
            })?;
            let base = self.ctxs[b];
            if let Some(p) = self.cc("infer.suffix_use", |el| el.closed_use_at(p0, base))? {
                self.check(p, e, e, ts[0])?;
                self.infer_memo.insert(key, (ts[0], p));
                return Ok((ts[0], p))
            }
        }
        let name = match self.read(e) {
            Expr::Local { .. } => "infer.local",
            Expr::Sort { .. } => "infer.sort",
            Expr::Const { .. } => "infer.const",
            Expr::App { .. } => "infer.app",
            Expr::Lambda { .. } | Expr::Pi { .. } => "infer.binder",
            Expr::Proj { .. } => "infer.proj",
            Expr::NatLit { .. } | Expr::StringLit { .. } => "infer.lit",
            _ => "infer.other",
        };
        let r = self.cc(name, |el| el.infer_rule(e))?;
        self.check(r.1, e, e, r.0)?;
        if self.tc.infer(e, nanoda_lib::tc::InferFlag::InferOnly) != r.0 {
            self.type_mismatches += 1;
        }
        self.infer_memo.insert(key, r);
        Ok(r)
    }

    fn infer_rule(&mut self, e: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        Ok(match self.read(e) {
            Expr::Local { id: FVarId::DbjLevel(k), binder_type, .. } => {
                let (k, d) = (k as usize, self.d());
                if k >= d {
                    return Err("fvar out of scope".into())
                }
                let g = self.ctx();
                let p = mm(self.g.lean.bvar_rule(&mut self.g.env, g, d - 1 - k))?;
                let here = self.locals[k];
                let Expr::Local { binder_type: ctx_ty, .. } = self.read(here) else { unreachable!() };
                (binder_type, self.cast(p, ctx_ty, binder_type)?)
            }
            Expr::Sort { level, .. } => {
                let pl = self.level_equiv(level, level)?;
                let (g, l) = (self.ctx(), self.trl(level)?);
                let p = mm(self.g.lean.sort_df(&mut self.g.env, g, l, l, pl))?;
                let s = self.tc.ctx.succ(level);
                (self.tc.ctx.mk_sort(s), p)
            }
            Expr::Const { name, levels, .. } => self.const_df(e, name, levels, levels)?,
            Expr::App { .. } => self.app_cong(e, e)?,
            Expr::Lambda { .. } | Expr::Pi { .. } => self.binder_cong(e, e)?,
            Expr::Let { val, body, .. } => {
                let b = self.tc.ctx.inst(body, &[val]);
                self.infer(b)?
            }
            Expr::Proj { idx, structure, .. } => {
                let p = self.proj_df(idx, structure, None)?;
                let t = self.tc.infer(e, nanoda_lib::tc::InferFlag::InferOnly);
                (t, self.proj_cast(p, e, t)?)
            }
            Expr::NatLit { ptr, .. } => {
                let n = self.tc.ctx.read_bignum(ptr).unwrap().clone();
                let p = self.lit_unfold(&n)?;
                let Some(nat) = self.tc.ctx.nat_type() else { return Err("a Nat literal without Nat".into()) };
                (nat, mm(self.g.lean.refl_l(&mut self.g.env, p))?)
            }
            Expr::StringLit { .. } => {
                let x = self.str_expand(e)?;
                self.infer(x)?
            }
            _ => return Err(format!("cannot type {}", self.show(e))),
        })
    }

    /// `Γ ⊢ c ls ≡ c ls' : T[ls]`.
    fn const_df(&mut self, e: ExprPtr<'t>, name: NamePtr<'t>, ls: nanoda_lib::util::LevelsPtr<'t>, ls2: nanoda_lib::util::LevelsPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        let s = self.g.lean_name(self.tc, name);
        let Some(ci) = self.g.consts.get(&s).cloned() else { return Err(format!("unknown constant {s}")) };
        let Some(d) = self.tc.env.get_declar(&name) else { return Err(format!("constant {s} not in scope")) };
        let info = *d.info();
        let ty = self.tc.ctx.subst_expr_levels(info.ty, info.uparams, ls);
        let g = self.ctx();
        let a: Vec<LevelPtr<'t>> = self.tc.ctx.read_levels(ls).to_vec();
        let b: Vec<LevelPtr<'t>> = self.tc.ctx.read_levels(ls2).to_vec();
        let mut args = vec![g];
        for &l in &a {
            args.push(self.trl(l)?);
        }
        let p = match ci.kind {
            ConstKind::Opaque | ConstKind::Ind { .. } | ConstKind::Ctor { .. } | ConstKind::Rec { .. } => {
                let mut hyps = Vec::new();
                for (&l, &l2) in a.iter().zip(&b) {
                    args.push(self.trl(l2)?);
                    hyps.push(self.level_equiv(l, l2)?);
                }
                mm(self.g.env.thm(ci.ty_thm, &args, &hyps))?
            }
            ConstKind::Def => {
                if ls != ls2 && a.iter().zip(&b).any(|(&x, &y)| x != y) {
                    return Err(format!("constDF for the definition {s} at different levels is not supported yet"))
                }
                let p = mm(self.g.env.thm(ci.ty_thm, &args, &[]))?;
                let target = self.deq(e, e, ty)?;
                mm(self.g.env.convert(p, target))?
            }
        };
        Ok((ty, p))
    }

    /// Congruence of two application spines of the same length (`x == y` for plain typing),
    /// mirroring nanoda's `infer_app`. Proves `Γ ⊢ x ≡ y : τ(x)`.
    fn app_cong(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        let (f, xs) = self.tc.ctx.unfold_apps(x);
        let (g, ys) = self.tc.ctx.unfold_apps(y);
        if xs.len() != ys.len() {
            return Err("app congruence: different numbers of arguments".into())
        }
        let (mut ft, mut pf) = self.infer(f)?;
        if f != g {
            pf = self.defeq(f, g)?;
        }
        for (&a, &b) in xs.iter().zip(&ys) {
            (ft, pf) = self.app_step(ft, pf, a, if a == b { None } else { Some(b) })?;
        }
        Ok((ft, pf))
    }

    /// Given `pf: Γ ⊢ f ≡ g : ft`, prove `Γ ⊢ f a ≡ g b : B[a]` (with `b = a` if `None`).
    fn app_step(&mut self, ft: ExprPtr<'t>, pf: P, a: ExprPtr<'t>, b: Option<ExprPtr<'t>>) -> R<(ExprPtr<'t>, P)> {
        let pa = match b {
            None => self.infer(a)?.1,
            Some(b) => self.defeq(a, b)?,
        };
        self.app_step_p(ft, pf, a, pa)
    }

    /// `app_step` with the argument's proof given: `pa: Γ ⊢ a ≡ b : τ(a)`.
    fn app_step_p(&mut self, ft: ExprPtr<'t>, pf: P, a: ExprPtr<'t>, pa: P) -> R<(ExprPtr<'t>, P)> {
        let (ft, pf) = self.as_pi(pf, ft)?;
        let Expr::Pi { binder_type, body, .. } = self.read(ft) else { unreachable!() };
        let at = self.infer(a)?.0;
        let pa = self.cast(pa, at, binder_type)?;
        let p = mm(self.g.lean.app_df(&mut self.g.env, pf, pa))?;
        Ok((self.tc.ctx.inst(body, &[a]), p))
    }

    /// Congruence of two `Pi`s or two `Lambda`s, one binder at a time (`x == y` for typing).
    fn binder_cong(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        let (is_pi, name, style, a1, b1, a2, b2) = match (self.read(x), self.read(y)) {
            (
                Expr::Pi { binder_name, binder_style, binder_type: a1, body: b1, .. },
                Expr::Pi { binder_type: a2, body: b2, .. },
            ) => (true, binder_name, binder_style, a1, b1, a2, b2),
            (
                Expr::Lambda { binder_name, binder_style, binder_type: a1, body: b1, .. },
                Expr::Lambda { binder_type: a2, body: b2, .. },
            ) => (false, binder_name, binder_style, a1, b1, a2, b2),
            _ => return Err("binder congruence on non-binders".into()),
        };
        let (sa, mut pa) = self.infer(a1)?;
        if a1 != a2 {
            pa = self.defeq(a1, a2)?;
        }
        let (u, pa) = self.as_sort(pa, sa)?;
        let d = self.d() as u16;
        let xl = self.open(name, style, a1)?;
        let (bx, by) = (self.tc.ctx.inst(b1, &[xl]), self.tc.ctx.inst(b2, &[xl]));
        let res = (|| {
            self.body_handle(x, bx)?;
            let (bt, mut pb) = self.infer(bx)?;
            if bx != by {
                pb = self.defeq(bx, by)?;
            }
            if is_pi {
                let (v, pb) = self.as_sort(pb, bt)?;
                let p = mm(self.g.lean.forall_df(&mut self.g.env, pa, pb))?;
                let l = self.tc.ctx.imax(u, v);
                Ok((self.tc.ctx.mk_sort(l), p))
            } else {
                let p = mm(self.g.lean.lam_df(&mut self.g.env, pa, pb))?;
                let bt = self.tc.ctx.abstr_levels(bt, d);
                Ok((self.tc.ctx.mk_pi(name, style, a1, bt), p))
            }
        })();
        self.close();
        res
    }

    // ------------------------------------------------------------------ structures

    /// The structure type `S ls ps` of `s` (its type in weak head normal form), with `s` typed at it.
    fn struct_type(&mut self, s: ExprPtr<'t>) -> R<(ExprPtr<'t>, P, String, nanoda_lib::util::LevelsPtr<'t>, Vec<ExprPtr<'t>>)> {
        let (st, ps) = self.infer(s)?;
        let w = self.tc.whnf(st);
        let ps = self.cast(ps, st, w)?;
        let Some((_, name, levels, args)) = self.tc.ctx.unfold_const_apps(w) else {
            return Err(format!("not a structure type: {}", self.show(w)))
        };
        Ok((w, ps, self.g.lean_name(self.tc, name), levels, args))
    }

    /// `Γ ⊢ s.i ≡ s2.i : F_i` by the field's typing axiom (`s2 = s` if `None`).
    fn proj_df(&mut self, idx: usize, s: ExprPtr<'t>, s2: Option<ExprPtr<'t>>) -> R<P> {
        let s2 = match s2 {
            None => None,
            Some(s2) => Some((s2, self.defeq(s, s2)?)),
        };
        self.proj_df_p(idx, s, s2)
    }

    /// `proj_df` with the structures' proof given: `Γ ⊢ s ≡ s2 : τ(s)`.
    fn proj_df_p(&mut self, idx: usize, s: ExprPtr<'t>, s2: Option<(ExprPtr<'t>, P)>) -> R<P> {
        let (_, ps, sname, levels, params) = self.struct_type(s)?;
        let Some(si) = self.g.structs.get(&sname).cloned() else { return Err(format!("unknown structure {sname}")) };
        let (mut th, needs_sort) = si.df[idx];
        let pe = match s2 {
            None => ps,
            Some((_, q)) => {
                let st = self.infer(s)?.0;
                let w = self.tc.whnf(st);
                self.cast(q, st, w)?
            }
        };
        let g = self.ctx();
        let ls: Vec<LevelPtr<'t>> = self.tc.ctx.read_levels(levels).to_vec();
        let mut args = vec![g];
        let mut lvls = vec![g];
        for &l in &ls {
            let m = self.trl(l)?;
            args.push(m);
            lvls.push(m);
        }
        let pts: Vec<E> = params.iter().map(|&p| self.tr(p)).collect::<R<_>>()?;
        args.extend(&pts);
        let (e, e2) = (self.tr(s)?, match s2 { None => self.tr(s)?, Some((s2, _)) => self.tr(s2)? });
        args.push(e);
        args.push(e2);
        let mut hyps = Vec::new();
        if needs_sort {
            let l = self.g.env.subst(si.sort, &lvls);
            let z = self.g.env.app_n("lz", &[]);
            let one = self.g.env.app_n("ls", &[z]);
            let m = self.g.env.app_n("lmax", &[one, l]);
            let gg = &mut *self.g;
            match (mm(gg.lv.equiv(&gg.lean, &mut gg.env, m, l)), &si.df_prop[idx]) {
                (Ok(p), _) => hyps.push(p),
                // from a proposition: the fields up to `idx` must be propositions at these levels
                (Err(_), Some((thp, fls))) => {
                    th = *thp;
                    for &fl in fls {
                        let fl = gg.env.subst(fl, &lvls);
                        hyps.push(mm(gg.lv.equiv(&gg.lean, &mut gg.env, fl, z)).map_err(|e| format!("projection {idx} of {sname} from a proposition: {e}"))?);
                    }
                }
                (Err(e), None) => return Err(format!("projection {idx} of {sname} from a proposition: {e}")),
            }
        }
        hyps.push(pe);
        // the field type, with parameters and earlier projections substituted outermost first
        // (the lemma's `inst` premises, as the spec's `pinst`/`qinst`)
        let n = si.np + idx;
        let mut cur = self.g.env.subst(si.field_tys[idx], &lvls);
        for j in 0..n {
            let a = if j < si.np { pts[j] } else {
                let b = self.g.env.app(si.blk, &[]);
                self.g.lean.proj(&mut self.g.env, b, j - si.np, e)
            };
            let (r, pr) = mm(self.g.lean.inst(&mut self.g.env, n - 1 - j, cur, a))?;
            args.push(r);
            hyps.push(pr);
            cur = r;
        }
        mm(self.g.env.thm(th, &args, &hyps))
    }

    /// Cast `p`, a `proj_df` proof about the projection `e`, to `to`. The axiom's type is the
    /// field type (`proj_field_type`), usually nanoda's own type of `e`, and `to` may differ
    /// from both, for example when it comes from a typing handle.
    fn proj_cast(&mut self, p: P, e: ExprPtr<'t>, to: ExprPtr<'t>) -> R<P> {
        let (_, _, _, t) = self.g.lean.deq_parts(&mut self.g.env, p);
        if t == self.tr(to)? {
            return Ok(p)
        }
        let t0 = self.tc.infer(e, nanoda_lib::tc::InferFlag::InferOnly);
        if t == self.tr(t0)? {
            return self.cast(p, t0, to)
        }
        let Expr::Proj { idx, structure, .. } = self.read(e) else { return Err("proj_cast: not a projection".into()) };
        let t1 = self.proj_field_type(idx, structure)?;
        if t == self.tr(t1)? {
            return self.cast(p, t1, to)
        }
        // a stage-B lemma states the field type with its annotations consumed (`optParam`,
        // `autoParam`, ...), as the block's data has it
        let t2 = crate::induct::consume_annots(self, t1);
        if t == self.tr(t2)? {
            return self.cast(p, t2, to)
        }
        Err(format!("internal: projection typed at an unexpected type: {}", self.g.show(t)))
    }

    /// The type the field axiom gives `s.idx`: the constructor's field type instantiated with
    /// the parameters of `struct_type(s)` and the earlier projections, without reducing (as
    /// MM0 substitution does). nanoda's `infer_proj` does the same with its own type of `s`,
    /// which can differ syntactically from ours (a typing handle).
    fn proj_field_type(&mut self, idx: usize, s: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        let (w, ..) = self.struct_type(s)?;
        let Some((_, name, levels, params)) = self.tc.ctx.unfold_const_apps(w) else { return Err("not a structure type".into()) };
        let env = self.tc.env;
        let Some(ind) = env.get_structure(&name, true) else { return Err("not a structure".into()) };
        let Some(nanoda_lib::env::ConstructorData { info, .. }) = env.get_constructor(&ind.all_ctor_names[0]) else {
            return Err("no constructor".into())
        };
        let mut t = self.tc.ctx.subst_declar_info_levels(*info, levels);
        let projs: Vec<ExprPtr<'t>> = (0..idx).map(|j| self.tc.ctx.mk_proj(ind.info.name, j, s)).collect();
        for &a in params[..ind.num_params as usize].iter().chain(&projs) {
            let Expr::Pi { body, .. } = self.read(t) else { return Err("constructor type too short".into()) };
            t = self.tc.ctx.inst(body, &[a]);
        }
        let Expr::Pi { binder_type, .. } = self.read(t) else { return Err("constructor type too short".into()) };
        Ok(binder_type)
    }

    /// `Γ ⊢ x ≡ S.mk ps (x.0) … (x.n) : S ls ps` by structure eta, with the expansion nanoda builds.
    fn struct_eta(&mut self, x: ExprPtr<'t>) -> R<(ExprPtr<'t>, ExprPtr<'t>, P)> {
        let (w, px, sname, levels, params) = self.struct_type(x)?;
        let Some(si) = self.g.structs.get(&sname).cloned() else { return Err(format!("unknown structure {sname}")) };
        let Some(eta) = si.eta else { return Err(format!("no eta for {sname}")) };
        let Some(expanded) = self.tc.expand_eta_struct_aux(w, x) else { return Err("eta expansion failed".into()) };
        let g = self.ctx();
        let mut args = vec![g];
        for &l in self.tc.ctx.read_levels(levels).to_vec().iter() {
            args.push(self.trl(l)?);
        }
        for &p in &params {
            args.push(self.tr(p)?);
        }
        args.push(self.tr(x)?);
        let p = mm(self.g.env.thm(eta, &args, &[px]))?;
        let want = self.deq(x, expanded, w)?;
        Ok((expanded, w, mm(self.g.env.convert(p, want))?))
    }

    // ------------------------------------------------------------------ defeq

    /// `Γ ⊢ x ≡ y : τ(x)`.
    pub fn defeq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> R<P> {
        if x == y {
            return Ok(self.infer(x)?.1)
        }
        let key = (x, y, self.ctx());
        if let Some(&p) = self.defeq_memo.get(&key) {
            return Ok(p)
        }
        if self.d() > 0 && !self.tc.ctx.has_fvars(x) && !self.tc.ctx.has_fvars(y) {
            let (p0, t0) = self.at_top(|el| Ok((el.defeq(x, y)?, el.infer(x)?.0)))?;
            if let Some(p) = self.cc("defeq.closed_use", |el| el.closed_use(p0))? {
                let p = self.at_type_of(x, p, t0)?;
                self.defeq_memo.insert(key, p);
                return Ok(p)
            }
        } else if let Some(top) = self.prefix_top(&[x, y]) {
            let (p0, t0) = self.with_prefix(top, |el| Ok((el.defeq(x, y)?, el.infer(x)?.0)))?;
            let p = self.cc("defeq.weaken", |el| el.weaken(p0, top))?;
            let p = self.at_type_of(x, p, t0)?;
            self.defeq_memo.insert(key, p);
            return Ok(p)
        } else if let b @ 1.. = self.suffix_base(&[x, y]) {
            let (ts, p0) = self.with_suffix(b, &[x, y], |el, es| {
                let p = el.defeq(es[0], es[1])?;
                Ok((vec![el.infer(es[0])?.0], p))
            })?;
            let base = self.ctxs[b];
            if let Some(p) = self.cc("defeq.suffix_use", |el| el.closed_use_at(p0, base))? {
                let p = self.at_type_of(x, p, ts[0])?;
                self.defeq_memo.insert(key, p);
                return Ok(p)
            }
        }
        let Some((swapped, why)) = self.tc.def_eq_why(x, y) else {
            return Err(format!("not defeq:\n  {}\n  {}", self.show(x), self.show(y)))
        };
        if self.g.env.num_pfs() > self.pf_limit {
            return Err("proof too large (see LEAN0_MAX_PROOF_NODES)".into())
        }
        if self.nest > 20_000 {
            return Err(format!("defeq nesting too deep at\n  {}\n  {}", self.show(x), self.show(y)))
        }
        if self.trace {
            let (a, b) = (self.show(x), self.show(y));
            eprintln!("{:w$}defeq {why:?} swapped={swapped}\n{:w$}  {a}\n{:w$}  {b}", "", "", "", w = self.nest);
        }
        self.nest += 1;
        let (n0, t0, why_s) = (self.g.env.num_pfs(), std::time::Instant::now(), self.profile.map(|_| format!("{why:?}")));
        let p = self.cc(why_name(&why), |el| el.defeq_main(x, y, swapped, why));
        self.nest -= 1;
        if let (Some(min), Some(why_s)) = (self.profile, why_s) {
            let n = self.g.env.num_pfs() - n0;
            if n >= min {
                let (a, b) = (self.show(x), self.show(y));
                let cut = |s: &str, k: usize| s.chars().take(k).collect::<String>();
                eprintln!("profile: {:w$}{n} nodes {} ms at depth {}: {} | {} | {}", "", t0.elapsed().as_millis(), self.d(), cut(&why_s, 30), cut(&a, 200), cut(&b, 200), w = self.nest);
            }
        }
        let p = p?;
        let tx = self.infer(x)?.0;
        self.check(p, x, y, tx)?;
        self.defeq_memo.insert(key, p);
        Ok(p)
    }

    fn defeq_main(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, swapped: bool, why: DefEqWhy<'t>) -> R<P> {
        Ok(if swapped {
            let p = self.defeq_rule(y, x, why)?;
            let p = mm(self.g.lean.symm(&mut self.g.env, p))?;
            let (ty, tx) = (self.infer(y)?.0, self.infer(x)?.0);
            self.cast(p, ty, tx)?
        } else {
            self.defeq_rule(x, y, why)?
        })
    }

    fn defeq_rule(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, why: DefEqWhy<'t>) -> R<P> {
        match why {
            DefEqWhy::Alpha | DefEqWhy::Local => {
                if self.tr(x)? != self.tr(y)? {
                    return Err(format!("{why:?}: translations differ"))
                }
                Ok(self.infer(x)?.1)
            }
            DefEqWhy::Sort => {
                let (Expr::Sort { level: l1, .. }, Expr::Sort { level: l2, .. }) = (self.read(x), self.read(y)) else {
                    return Err("Sort rule on non-sorts".into())
                };
                let pl = self.level_equiv(l1, l2)?;
                let (g, a, b) = (self.ctx(), self.trl(l1)?, self.trl(l2)?);
                mm(self.g.lean.sort_df(&mut self.g.env, g, a, b, pl))
            }
            DefEqWhy::Binder => {
                let (t, p) = self.binder_cong(x, y)?;
                self.at_type_of(x, p, t)
            }
            DefEqWhy::App | DefEqWhy::ConstApp => {
                let (t, p) = self.app_cong(x, y)?;
                self.at_type_of(x, p, t)
            }
            DefEqWhy::Const => {
                let (Expr::Const { name, levels: l1, .. }, Expr::Const { levels: l2, .. }) = (self.read(x), self.read(y)) else {
                    return Err("Const rule on non-constants".into())
                };
                let (t, p) = self.const_df(x, name, l1, l2)?;
                self.at_type_of(x, p, t)
            }
            DefEqWhy::Reduce(x2, y2) => {
                let tx = self.infer(x)?.0;
                let rx = self.reduce(x, x2)?;
                let m = self.defeq(x2, y2)?;
                let tx2 = self.infer(x2)?.0;
                let m = self.cast(m, tx2, tx)?;
                let ry = self.reduce(y, y2)?;
                let ry = mm(self.g.lean.symm(&mut self.g.env, ry))?;
                let ty = self.infer(y)?.0;
                let ry = self.cast(ry, ty, tx)?;
                let p = mm(self.g.lean.trans(&mut self.g.env, rx, m))?;
                mm(self.g.lean.trans(&mut self.g.env, p, ry))
            }
            DefEqWhy::ProofIrrel => {
                let (tx, ph) = self.infer(x)?;
                let (stp, pp) = self.infer(tx)?;
                let (l, pp) = self.as_sort(pp, stp)?;
                let zero = self.tc.ctx.zero();
                let pp = if l == zero {
                    pp
                } else {
                    let pl = self.level_equiv(l, zero)?;
                    let (g, a, b) = (self.ctx(), self.trl(l)?, self.trl(zero)?);
                    let q = mm(self.g.lean.sort_df(&mut self.g.env, g, a, b, pl))?;
                    mm(self.g.lean.defeq_df(&mut self.g.env, q, pp))?
                };
                let (ty, ph2) = self.infer(y)?;
                let ph2 = self.cast(ph2, ty, tx)?;
                mm(self.g.lean.proof_irrel(&mut self.g.env, pp, ph, ph2))
            }
            DefEqWhy::Eta(ylam) => {
                let tx = self.infer(x)?.0;
                let e = self.defeq(x, ylam)?;
                let (ty, py) = self.infer(y)?;
                let (w, py) = self.as_pi(py, ty)?;
                let pe = mm(self.g.lean.eta(&mut self.g.env, py))?;
                let (_, lhs, _, _) = self.g.lean.deq_parts(&mut self.g.env, pe);
                if lhs != self.tr(ylam)? {
                    return Err("eta: expansion does not match the kernel's".into())
                }
                let pe = self.cast(pe, w, tx)?;
                mm(self.g.lean.trans(&mut self.g.env, e, pe))
            }
            DefEqWhy::Proj => {
                let (Expr::Proj { idx, structure: s1, .. }, Expr::Proj { structure: s2, .. }) = (self.read(x), self.read(y)) else {
                    return Err("Proj rule on non-projections".into())
                };
                if self.tc.def_eq(s1, s2) {
                    let p = self.proj_df(idx, s1, Some(s2))?;
                    let tx = self.infer(x)?.0;
                    self.proj_cast(p, x, tx)
                } else {
                    // nanoda compared the fields of the reduced structures
                    let Some((x2, Step::Proj)) = self.head_step(x) else { return Err("Proj: structure does not reduce".into()) };
                    let Some((y2, Step::Proj)) = self.head_step(y) else { return Err("Proj: structure does not reduce".into()) };
                    self.defeq_rule(x, y, DefEqWhy::Reduce(x2, y2))
                }
            }
            DefEqWhy::EtaStruct => {
                // y is a constructor application; expand x
                let tx = self.infer(x)?.0;
                let (ex, w, pe) = self.struct_eta(x)?;
                let pe = self.cast(pe, w, tx)?;
                let q = self.defeq(ex, y)?;
                let tex = self.infer(ex)?.0;
                let q = self.cast(q, tex, tx)?;
                mm(self.g.lean.trans(&mut self.g.env, pe, q))
            }
            DefEqWhy::Unit => {
                let tx = self.infer(x)?.0;
                let ty = self.infer(y)?.0;
                let (ex, wx, px) = self.struct_eta(x)?;
                let (ey, wy, py) = self.struct_eta(y)?;
                let px = self.cast(px, wx, tx)?;
                let m = self.defeq(ex, ey)?;
                let tex = self.infer(ex)?.0;
                let m = self.cast(m, tex, tx)?;
                let py = mm(self.g.lean.symm(&mut self.g.env, py))?;
                let py = self.cast(py, wy, ty)?;
                let py = self.cast(py, ty, tx)?;
                let p = mm(self.g.lean.trans(&mut self.g.env, px, m))?;
                mm(self.g.lean.trans(&mut self.g.env, p, py))
            }
            DefEqWhy::NatZero => {
                let tx = self.infer(x)?.0;
                let (px, py) = (self.nat_zero_eq(x)?, self.nat_zero_eq(y)?);
                let py = mm(self.g.lean.symm(&mut self.g.env, py))?;
                let p = mm(self.g.lean.trans(&mut self.g.env, px, py))?;
                let nat = self.tc.ctx.nat_type().unwrap();
                self.cast(p, nat, tx)
            }
            DefEqWhy::NatSucc(xp, yp) => {
                let tx = self.infer(x)?.0;
                let Some(succ) = self.tc.ctx.c_nat_succ() else { return Err("Nat.succ is not declared".into()) };
                let (sx, sy) = (self.tc.ctx.mk_app(succ, xp), self.tc.ctx.mk_app(succ, yp));
                let (px, py) = (self.succ_eq(x, sx)?, self.succ_eq(y, sy)?);
                let (tsx, m) = self.app_cong(sx, sy)?;
                let nat = self.tc.ctx.nat_type().unwrap();
                let m = self.cast(m, tsx, nat)?;
                let py = mm(self.g.lean.symm(&mut self.g.env, py))?;
                let p = mm(self.g.lean.trans(&mut self.g.env, px, m))?;
                let p = mm(self.g.lean.trans(&mut self.g.env, p, py))?;
                self.cast(p, nat, tx)
            }
            DefEqWhy::StrLit => {
                // the literal's expansion reduces to `w`, and `w ≡ other`
                let lit_left = matches!(self.read(x), Expr::StringLit { .. });
                let (s, other) = if lit_left { (x, y) } else { (y, x) };
                let (w, ps) = self.str_whnf(s)?;
                let ts = self.infer(s)?.0;
                let q = self.defeq(w, other)?;
                let tw = self.infer(w)?.0;
                let q = self.cast(q, tw, ts)?;
                let p = mm(self.g.lean.trans(&mut self.g.env, ps, q))?;
                if lit_left {
                    Ok(p)
                } else {
                    let p = mm(self.g.lean.symm(&mut self.g.env, p))?;
                    let tx = self.infer(x)?.0;
                    self.cast(p, ts, tx)
                }
            }
            DefEqWhy::Unsupported(s) => Err(format!("unsupported defeq rule: {s}")),
        }
    }

    // ------------------------------------------------------------------ literals

    /// `Γ ⊢ lit n ≡ Nat.zero : Nat` if `n = 0`, else `Γ ⊢ lit n ≡ Nat.succ (lit (n-1)) : Nat`.
    fn lit_unfold(&mut self, n: &BigUint) -> R<P> {
        let Some(nl) = self.g.nat else { return Err("Nat literals need Nat.zero : Nat and Nat.succ : Nat → Nat".into()) };
        let g = self.ctx();
        if n.bits() == 0 {
            return mm(self.g.env.thm(nl.zero, &[g], &[]))
        }
        let m = n - 1u32;
        let (_, ps) = mm(self.g.bins.rel(&mut self.g.env, Rel::Succ, std::slice::from_ref(&m)))?;
        let (a, b) = (self.g.bins.num(&mut self.g.env, &m), self.g.bins.num(&mut self.g.env, n));
        mm(self.g.env.thm(nl.succ, &[g, a, b], &[ps]))
    }

    /// `Γ ⊢ x ≡ Nat.zero : Nat`, for `x` the literal `0` or `Nat.zero`.
    fn nat_zero_eq(&mut self, x: ExprPtr<'t>) -> R<P> {
        match self.read(x) {
            Expr::NatLit { .. } => self.lit_unfold(&BigUint::default()),
            _ => {
                let (tx, p) = self.infer(x)?;
                let nat = self.tc.ctx.nat_type().unwrap();
                self.cast(p, tx, nat)
            }
        }
    }

    /// `Γ ⊢ x ≡ sx : Nat` where `sx = Nat.succ x'` and `x` is `sx` or the literal `x' + 1`.
    fn succ_eq(&mut self, x: ExprPtr<'t>, sx: ExprPtr<'t>) -> R<P> {
        let nat = self.tc.ctx.nat_type().unwrap();
        if let Expr::NatLit { ptr, .. } = self.read(x) {
            let n = self.tc.ctx.read_bignum(ptr).unwrap().clone();
            let p = self.lit_unfold(&n)?;
            let want = self.deq(x, sx, nat)?;
            return mm(self.g.env.convert(p, want))
        }
        if self.tr(x)? != self.tr(sx)? {
            return Err("NatSucc: not a successor".into())
        }
        let (tx, p) = self.infer(x)?;
        self.cast(p, tx, nat)
    }

    /// `Γ ⊢ a ≡ c : τ(a)` from `a ≡ b` (asked of nanoda) and `p: Γ ⊢ b ≡ c : tb`.
    fn via(&mut self, a: ExprPtr<'t>, b: ExprPtr<'t>, p: P, tb: ExprPtr<'t>) -> R<P> {
        let ta = self.infer(a)?.0;
        let q = self.defeq(a, b)?;
        let p = self.cast(p, tb, ta)?;
        mm(self.g.lean.trans(&mut self.g.env, q, p))
    }

    /// The expansion `String.ofList [Char.ofNat n, ...]` of a string literal.
    fn str_expand(&mut self, e: ExprPtr<'t>) -> R<ExprPtr<'t>> {
        let Expr::StringLit { ptr, .. } = self.read(e) else { unreachable!() };
        self.tc.ctx.str_lit_to_constructor(ptr).ok_or_else(|| "string literals need String.ofList, Char.ofNat and List".to_string())
    }

    /// The weak head normal form `w` of a string literal's expansion (as nanoda's
    /// `str_lit_to_ctor_reducing`) and `Γ ⊢ s ≡ w : τ(s)`. The literal and its expansion
    /// have the same translation, so a reduction of the expansion proves it.
    fn str_whnf(&mut self, s: ExprPtr<'t>) -> R<(ExprPtr<'t>, P)> {
        let x = self.str_expand(s)?;
        let w = self.tc.whnf(x);
        Ok((w, self.reduce(x, w)?))
    }

    /// `Nat.succ a ≡ lit (n+1)` or `op a b ≡ r`, where `a` and `b` reduce to literals (or
    /// `Nat.zero`): congruence down to the literals, then the literal axiom.
    fn nat_step(&mut self, cur: ExprPtr<'t>) -> R<P> {
        let (f, args) = self.tc.ctx.unfold_apps(cur);
        let Expr::Const { name, .. } = self.read(f) else { unreachable!() };
        let op = self.g.lean_name(self.tc, name);
        let nat = self.tc.ctx.nat_type().unwrap();
        let (mut ft, mut pf) = self.infer(f)?;
        let mut vals = Vec::new();
        for &a in &args {
            let w = self.tc.whnf(a);
            let Some(v) = self.tc.ctx.get_bignum_from_expr(w) else { return Err("Nat operation: argument is not a literal".into()) };
            let mut pa = self.defeq(a, w)?;
            if !matches!(self.read(w), Expr::NatLit { .. }) {
                // `Nat.zero`, as the literal `0`
                let pz = self.lit_unfold(&v)?;
                let pz = mm(self.g.lean.symm(&mut self.g.env, pz))?;
                let ta = self.infer(a)?.0;
                let pz = self.cast(pz, nat, ta)?;
                pa = mm(self.g.lean.trans(&mut self.g.env, pa, pz))?;
            }
            (ft, pf) = self.app_step_p(ft, pf, a, pa)?;
            vals.push(v);
        }
        let pr = if op == "Nat.succ" {
            let p = self.lit_unfold(&(&vals[0] + 1u32))?;
            mm(self.g.lean.symm(&mut self.g.env, p))?
        } else {
            self.nat_op(&op, &vals[0], &vals[1])?
        };
        let (_, _, _, t) = self.g.lean.deq_parts(&mut self.g.env, pr);
        if self.tr(ft)? != t {
            return Err(format!("{op}: unexpected type"))
        }
        let p = mm(self.g.lean.trans(&mut self.g.env, pf, pr))?;
        let tcur = self.infer(cur)?.0;
        self.cast(p, ft, tcur)
    }

    /// `Γ ⊢ op (lit a) (lit b) ≡ r : T` by the first of the operation's theorems that applies.
    fn nat_op(&mut self, op: &str, a: &BigUint, b: &BigUint) -> R<P> {
        if op == "Nat.shiftRight" {
            if let Some(&eqs) = self.g.nat_eqs.get(op) {
                return self.nat_shr(eqs, a, b)
            }
        }
        let (Some(o), Some(ths)) = (natlit::op(op), self.g.nat_ops.get(op).cloned()) else {
            return Err(format!("no literal axioms for {op}"))
        };
        let g = self.ctx();
        for (ax, th) in o.axs.iter().zip(ths) {
            let Some(vals) = natlit::witness(op, ax.suffix, a, b)? else { continue };
            let val = |x: natlit::A| match x {
                natlit::A::V(i) => vals[i].clone(),
                natlit::A::N(k) => BigUint::from(k),
            };
            let mut hyps = Vec::new();
            for &(rel, xs) in ax.hyps {
                let ins: Vec<BigUint> = xs[..xs.len() - 1].iter().map(|&x| val(x)).collect();
                let (out, p) = mm(self.g.bins.rel(&mut self.g.env, rel, &ins))?;
                if out != val(xs[xs.len() - 1]) {
                    return Err(format!("internal: {op} {}: {rel:?} {ins:?} is {out}", ax.suffix))
                }
                hyps.push(p);
            }
            let mut targs = vec![g];
            for v in &vals {
                targs.push(self.g.bins.num(&mut self.g.env, v));
            }
            return mm(self.g.env.thm(th, &targs, &hyps))
        }
        Err(format!("internal: no literal axiom of {op} applies"))
    }

    /// `Γ ⊢ Nat.shiftRight (lit a) (lit b) ≡ lit (a >> b) : Nat`, a shift at a time from the
    /// equations `eqs` (`shr_eqs G Nat.shiftRight Nat.div`: the spec's `nat_shr_lit_z` and
    /// `nat_shr_lit_s`) and the divisions by 2.
    fn nat_shr(&mut self, eqs: ThId, a: &BigUint, b: &BigUint) -> R<P> {
        let k = natlit::small(b)?;
        let gc = self.ctx();
        let (Some(f), Some(fd), Some(nat)) = (self.g.const_term("Nat.shiftRight", &[]), self.g.const_term("Nat.div", &[]), self.g.const_term("Nat", &[])) else {
            return Err("internal: `Nat.shiftRight` without `Nat.div`".into())
        };
        let g = &mut *self.g;
        let num = |g: &mut Gen, n: &BigUint| g.bins.num(&mut g.env, n);
        let peqs = mm(g.env.thm(eqs, &[gc], &[]))?;
        let na = num(g, a);
        let mut p = mm(g.env.thm_n("nat_shr_lit_z", &[gc, f, fd, na], &[peqs]))?;
        let two = BigUint::from(2u32);
        let mut c = a.clone();
        for i in 0..k {
            let bi = BigUint::from(i);
            let (bi1, ps) = mm(self.g.bins.rel(&mut self.g.env, Rel::Succ, &[bi.clone()]))?;
            let c2 = &c / &two;
            let pd = self.nat_op("Nat.div", &c, &two)?;
            let g = &mut *self.g;
            let args = [gc, f, fd, na, num(g, &bi), num(g, &bi1), num(g, &c), num(g, &c2)];
            p = mm(g.env.thm_n("nat_shr_lit_s", &args, &[peqs, ps, p, pd]))?;
            c = c2;
        }
        let g = &mut *self.g;
        let (la, lb, lc) = (g.env.app(g.bins.lit, &[na]), num(g, b), num(g, &c));
        let (lb, lc) = (g.env.app(g.bins.lit, &[lb]), g.env.app(g.bins.lit, &[lc]));
        let fa = g.lean.app(&mut g.env, f, la);
        let lhs = g.lean.app(&mut g.env, fa, lb);
        let want = g.lean.deq(&mut g.env, gc, lhs, lc, nat);
        mm(g.env.convert(p, want))
    }

    // ------------------------------------------------------------------ reduction

    fn head_step(&mut self, e: ExprPtr<'t>) -> Option<(ExprPtr<'t>, Step)> {
        let (f, args) = self.tc.ctx.unfold_apps(e);
        match self.read(f) {
            Expr::Lambda { body, .. } if !args.is_empty() => {
                let b = self.tc.ctx.inst(body, &args[..1]);
                Some((self.tc.ctx.foldl_apps(b, args.into_iter().skip(1)), Step::Beta))
            }
            Expr::Let { val, body, .. } => {
                let b = self.tc.ctx.inst(body, &[val]);
                Some((self.tc.ctx.foldl_apps(b, args.into_iter()), Step::Zeta))
            }
            Expr::Proj { idx, structure, .. } => {
                let s2 = self.tc.whnf(structure);
                let field = self.tc.reduce_proj_core(idx, s2)?;
                Some((self.tc.ctx.foldl_apps(field, args.into_iter()), Step::Proj))
            }
            Expr::Const { name, levels, .. } => {
                if let Some(r) = self.tc.reduce_quot(name, &args) {
                    Some((r, Step::Quot))
                } else if let Some(r) = self.tc.reduce_rec(name, levels, &args) {
                    Some((r, Step::Iota))
                } else if let Some(r) = (!self.tc.ctx.has_fvars(e)).then(|| self.tc.try_reduce_nat(e)).flatten() {
                    // Before unfolding, as in nanoda's `whnf`. But the reductions we replay
                    // come from lazy delta, which computes on literals only in closed terms
                    // (`delta_try_nat`), and from `whnf` of closed terms.
                    Some((r, Step::Nat))
                } else {
                    self.tc.unfold_def(e).map(|e2| (e2, Step::Delta))
                }
            }
            Expr::Sort { level, .. } if args.is_empty() => {
                let l2 = self.tc.ctx.simplify(level);
                (l2 != level).then(|| (self.tc.ctx.mk_sort(l2), Step::SortSimp))
            }
            _ => None,
        }
    }

    /// `Γ ⊢ x ≡ target : τ(x)`, where `target` is reached from `x` by head reduction steps.
    fn reduce(&mut self, x: ExprPtr<'t>, target: ExprPtr<'t>) -> R<P> { self.cc("reduce", |el| el.reduce_main(x, target)) }

    fn reduce_main(&mut self, x: ExprPtr<'t>, target: ExprPtr<'t>) -> R<P> {
        let (tx, mut p) = self.infer(x)?;
        let mut cur = x;
        let mut steps = 0;
        while cur != target {
            steps += 1;
            if steps > MAX_REDUCE_STEPS {
                return Err("reduction did not reach the kernel's reduct".into())
            }
            if self.trace && steps % 1000 == 0 {
                let (a, b) = (self.show(cur), self.show(target));
                eprintln!("reduce: {steps} steps at\n  {}\ntowards\n  {}", &a[..a.len().min(400)], &b[..b.len().min(400)]);
            }
            let Some((next, kind)) = self.head_step(cur) else {
                // Our steps computed on literals where the kernel's unfolded the operation
                // (`head_step` computes in every closed term, lazy delta does not): `cur` is
                // a literal, `target` an unfolding of the same number. Ask for it directly.
                if cur != x && matches!(self.read(cur), Expr::NatLit { .. }) {
                    let q = self.defeq(cur, target)?;
                    let tcur = self.infer(cur)?.0;
                    let q = self.cast(q, tcur, tx)?;
                    return mm(self.g.lean.trans(&mut self.g.env, p, q))
                }
                return Err(format!("stuck reducing\n  {}\ntowards\n  {}", self.show(cur), self.show(target)))
            };
            match kind {
                Step::Zeta => {}
                Step::Delta => {
                    let want = self.deq(x, next, tx)?;
                    p = mm(self.g.env.convert(p, want))?;
                }
                Step::Beta | Step::SortSimp | Step::Proj | Step::Quot | Step::Iota | Step::Nat => {
                    let s = self.cc(step_name(kind), |el| el.step_proof(cur, kind))?;
                    let tcur = self.infer(cur)?.0;
                    // the step may prove its reduct up to unfolding (e.g. an iota rule's `def`)
                    let want = self.deq(cur, next, tcur)?;
                    let s = mm(self.g.env.convert(s, want))?;
                    let s = self.cast(s, tcur, tx)?;
                    p = mm(self.g.lean.trans(&mut self.g.env, p, s))?;
                }
            }
            cur = next;
        }
        Ok(p)
    }

    /// `(s.i) args ≡ field args`: the structure reduces to a constructor application.
    fn proj_step(&mut self, cur: ExprPtr<'t>) -> R<P> {
        let (f, args) = self.tc.ctx.unfold_apps(cur);
        let Expr::Proj { ty_name, idx, structure, .. } = self.read(f) else { unreachable!() };
        let s2 = self.tc.whnf(structure);
        let mut q = self.defeq(structure, s2)?;
        // nanoda expands a string literal (as `reduce_proj_core` does)
        let s2 = if let Expr::StringLit { .. } = self.read(s2) {
            let (w, pw) = self.str_whnf(s2)?;
            let (ts, ts2) = (self.infer(structure)?.0, self.infer(s2)?.0);
            let pw = self.cast(pw, ts2, ts)?;
            q = mm(self.g.lean.trans(&mut self.g.env, q, pw))?;
            w
        } else {
            s2
        };
        let proj2 = self.tc.ctx.mk_proj(ty_name, idx, s2);
        let tf = self.infer(f)?.0;
        // s.i ≡ s2.i by congruence, then s2.i ≡ field by the reduction axiom
        let p1 = self.proj_df_p(idx, structure, Some((s2, q)))?;
        self.infer(proj2)?;
        let sname = self.g.lean_name(self.tc, ty_name);
        let si = self.g.structs[&sname].clone();
        let (_, ctor_args) = self.tc.ctx.unfold_apps(s2);
        let Some((_, _, clevels, _)) = self.tc.ctx.unfold_const_apps(s2) else { return Err("projection of a non-constructor".into()) };
        let g = self.ctx();
        let mut a = vec![g];
        for &l in self.tc.ctx.read_levels(clevels).to_vec().iter() {
            a.push(self.trl(l)?);
        }
        if ctor_args.len() != si.nf + si.np {
            return Err(format!("projection {idx} of {sname}: the constructor's argument count"))
        }
        // `proj_ok`'s premises (as `proj_df_p`)
        let lvls: Vec<E> = a.clone();
        let (mut th, needs_sort) = si.red[idx];
        let mut hyps = Vec::new();
        if needs_sort {
            let l = self.g.env.subst(si.sort, &lvls);
            let z = self.g.env.app_n("lz", &[]);
            let one = self.g.env.app_n("ls", &[z]);
            let m = self.g.env.app_n("lmax", &[one, l]);
            let gg = &mut *self.g;
            match (mm(gg.lv.equiv(&gg.lean, &mut gg.env, m, l)), &si.red_prop[idx], &si.df_prop[idx]) {
                (Ok(p), _, _) => hyps.push(p),
                (Err(_), Some(thp), Some((_, fls))) => {
                    th = *thp;
                    for &fl in fls {
                        let fl = gg.env.subst(fl, &lvls);
                        hyps.push(mm(gg.lv.equiv(&gg.lean, &mut gg.env, fl, z)).map_err(|e| format!("projection {idx} of {sname} from a proposition: {e}"))?);
                    }
                }
                (Err(e), _, _) => return Err(format!("projection {idx} of {sname} from a proposition: {e}")),
            }
        }
        // the closed equation (`proj_mk`, audit §4), its variables instantiated from the
        // bottom of its context (`instDF`): the parameters, then the fields, each typed at
        // its binder in the constructor's type as the schema has it
        let (cf, _) = self.tc.ctx.unfold_apps(s2);
        let cty = self.infer(cf)?.0;
        let mut cty = crate::induct::strip_pis(self, cty);
        let mut subst = Vec::new();
        for &x in &ctor_args {
            let Expr::Pi { binder_type, body, .. } = self.read(cty) else { return Err("the constructor's type is not a telescope over its arguments".into()) };
            subst.push((x, binder_type));
            cty = self.tc.ctx.inst(body, &[x]);
        }
        let tl3 = subst[si.np + idx].1;
        let mut p2 = mm(self.g.env.thm(th, &a, &hyps))?;
        let n = subst.len();
        for (j, &(x, bt)) in subst.iter().enumerate() {
            let (tx, px) = self.infer(x)?;
            let px = self.cast(px, tx, bt)?;
            p2 = mm(self.g.lean.inst_df(&mut self.g.env, n - 1 - j, px, p2))?;
        }
        let (_, le, _, te) = self.g.lean.deq_parts(&mut self.g.env, p2);
        if le != self.tr(proj2)? || te != self.tr(tl3)? {
            return Err(format!("projection {idx} of {sname}: the instance is not the expected one"))
        }
        let p1 = self.proj_cast(p1, f, tf)?;
        let p2 = self.cast(p2, tl3, tf)?;
        let mut pf = mm(self.g.lean.trans(&mut self.g.env, p1, p2))?;
        let mut ft = tf;
        for &x in &args {
            (ft, pf) = self.app_step(ft, pf, x, None)?;
        }
        let tcur = self.infer(cur)?.0;
        self.cast(pf, ft, tcur)
    }

    /// `sty G h A (h args) T` for a head `h` with the type `ty` (a `Π` telescope over `args`;
    /// a type of the head up to annotations: an inductive type's type as the schema's data
    /// has it, for `cwf_res`): each argument typed at its binder's type, `T` the rest.
    pub(crate) fn sty_spine_at(&mut self, h: ExprPtr<'t>, ty: ExprPtr<'t>, args: &[ExprPtr<'t>]) -> R<(ExprPtr<'t>, P)> {
        let mut ty = ty;
        let (g, he, te) = (self.ctx(), self.tr(h)?, self.tr(ty)?);
        let mut ps = mm(self.g.lean.sty_nil(&mut self.g.env, g, he, te))?;
        for &a in args {
            let Expr::Pi { binder_type, body, .. } = self.read(ty) else {
                return Err("reduction rule: the head's type is not a telescope over its arguments".into())
            };
            let (at, pa) = self.infer(a)?;
            let pa = self.cast(pa, at, binder_type)?;
            ps = mm(self.g.lean.sty_app(&mut self.g.env, ps, pa))?;
            ty = self.tc.ctx.inst(body, &[a]);
        }
        Ok((ty, ps))
    }

    /// `rec … major rest ≡ R_c … fields rest` (or the `Quot.lift`/`Quot.ind` rule): first the
    /// major premise is replaced by the constructor application nanoda found (by reduction,
    /// K or structure eta, all justified by asking nanoda `major ≡ major'`), then the axiom.
    fn iota_step(&mut self, cur: ExprPtr<'t>, kind: Step) -> R<P> {
        let (f, args) = self.tc.ctx.unfold_apps(cur);
        let Expr::Const { name, levels, .. } = self.read(f) else { unreachable!() };
        let fname = self.g.lean_name(self.tc, name);
        // a literal major premise becomes a constructor application, with `major_p` proving
        // `major ≡ major2`
        let mut major_p = None;
        let (major_idx, major2) = if kind == Step::Quot {
            let i = if fname == "Quot.lift" { 5 } else { 4 };
            (i, self.tc.whnf(args[i]))
        } else {
            let rec = self.tc.env.get_recursor(&name).cloned().unwrap();
            let i = rec.major_idx();
            let m = args[i];
            let m = self.tc.to_ctor_when_k(m, &rec).unwrap_or(m);
            let m = self.tc.whnf(m);
            match self.read(m) {
                Expr::NatLit { ptr, .. } => {
                    let n = self.tc.ctx.read_bignum(ptr).unwrap().clone();
                    let Some(c) = self.tc.ctx.nat_lit_to_constructor(ptr) else { return Err("Nat literal without constructors".into()) };
                    let p = self.lit_unfold(&n)?;
                    let nat = self.tc.ctx.nat_type().unwrap();
                    major_p = Some(self.via(args[i], m, p, nat)?);
                    (i, c)
                }
                Expr::StringLit { .. } => {
                    let (w, p) = self.str_whnf(m)?;
                    let tm = self.infer(m)?.0;
                    major_p = Some(self.via(args[i], m, p, tm)?);
                    (i, w)
                }
                _ => {
                    let ind = self.tc.ctx.get_major_induct(&rec).unwrap();
                    (i, self.tc.iota_try_eta_struct(ind, m))
                }
            }
        };
        let lhs = self.tc.ctx.foldl_apps(f, args[..=major_idx].iter().copied());
        let mut args2: Vec<ExprPtr<'t>> = args[..=major_idx].to_vec();
        args2[major_idx] = major2;
        let lhs2 = self.tc.ctx.foldl_apps(f, args2.iter().copied());
        let tl = self.infer(lhs)?.0;
        let p1 = if let Some(pm) = major_p {
            let head = self.tc.ctx.foldl_apps(f, args[..major_idx].iter().copied());
            let (ht, ph) = self.infer(head)?;
            let (t1, p1) = self.app_step_p(ht, ph, args[major_idx], pm)?;
            self.cast(p1, t1, tl)?
        } else if lhs == lhs2 {
            self.infer(lhs)?.1
        } else {
            self.app_cong(lhs, lhs2)?.1
        };
        // the axiom's arguments
        let g = self.ctx();
        let mut a = vec![g];
        for &l in self.tc.ctx.read_levels(levels).to_vec().iter() {
            a.push(self.trl(l)?);
        }
        let (mf, margs) = self.tc.ctx.unfold_apps(major2);
        let Expr::Const { name: cname, .. } = self.read(mf) else { return Err("major premise is not a constructor application".into()) };
        let p2 = if kind == Step::Quot {
            // the closed equation of the primitive (`quot_lift_mk`, `quot_ind_mk`; audit §4)
            let th = self.g.quot_red[&fname];
            self.quot_closed(th, f, &a, &args2[..major_idx], &margs, cname, lhs2, tl).map_err(|e| format!("reduction of {fname}: {e}"))?
        } else {
            let cl = self.g.lean_name(self.tc, cname);
            // the closed equation of the block's recursor rule (audit §4)
            let Some(&th) = self.g.iota_eq.get(&(fname.clone(), cl.clone())) else { return Err(format!("no iota rule {fname} {cl}")) };
            self.iota_closed(th, &fname, f, &a, &args2[..major_idx], &margs, cname, lhs2, tl)
                .map_err(|e| format!("iota of {fname} on {cl}: {e}"))?
        };
        let mut pf = mm(self.g.lean.trans(&mut self.g.env, p1, p2))?;
        let mut ft = tl;
        for &x in &args[major_idx + 1..] {
            (ft, pf) = self.app_step(ft, pf, x, None)?;
        }
        let tcur = self.infer(cur)?.0;
        self.cast(pf, ft, tcur)
    }

    /// The reduction of `Quot.lift` or `Quot.ind` (`f`, applied to `rargs` and to `Quot.mk`,
    /// `cname`, applied to `margs`) from the closed equation `th`: its variables are
    /// instantiated from the bottom of its context (`instDF`), the primitive's arguments each
    /// typed at its binder, then `a` at `α`. The instance has the primitive's `α`, `r` and
    /// level in `Quot.mk`: `lhs2` is equal to it by congruence. `a` is `Γ` and the levels.
    #[allow(clippy::too_many_arguments)]
    fn quot_closed(&mut self, th: mm0kit::env::ThId, f: ExprPtr<'t>, a: &[E], rargs: &[ExprPtr<'t>], margs: &[ExprPtr<'t>], cname: nanoda_lib::util::NamePtr<'t>, lhs2: ExprPtr<'t>, tl: ExprPtr<'t>) -> R<P> {
        let Some(&ae) = margs.get(2) else { return Err("Quot.mk is not applied to its three arguments".into()) };
        if rargs.len() < 4 {
            return Err("argument counts".into())
        }
        let mut subst = Vec::new();
        let mut ty = self.infer(f)?.0;
        for &x in rargs {
            let Expr::Pi { binder_type, body, .. } = self.read(ty) else { return Err("the primitive's type is not a telescope over its arguments".into()) };
            subst.push((x, binder_type));
            ty = self.tc.ctx.inst(body, &[x]);
        }
        subst.push((ae, rargs[0]));
        // the instance's left-hand side and type
        let Expr::Const { levels, .. } = self.read(f) else { unreachable!() };
        let l0 = self.tc.ctx.read_levels(levels)[0];
        let ls = self.tc.ctx.alloc_levels_slice(&[l0]);
        let mk = self.tc.ctx.mk_const(cname, ls);
        let major3 = self.tc.ctx.foldl_apps(mk, [rargs[0], rargs[1], ae].into_iter());
        let lhs3 = self.tc.ctx.foldl_apps(f, rargs.iter().copied().chain([major3]));
        let tl3 = if rargs.len() == 5 { rargs[2] } else { self.tc.ctx.foldl_apps(rargs[2], [major3].into_iter()) };
        let mut p = mm(self.g.env.thm(th, a, &[]))?;
        let n = subst.len();
        for (j, &(x, bt)) in subst.iter().enumerate() {
            let (tx, px) = self.infer(x)?;
            let px = self.cast(px, tx, bt)?;
            p = mm(self.g.lean.inst_df(&mut self.g.env, n - 1 - j, px, p))?;
        }
        let (_, le, _, te) = self.g.lean.deq_parts(&mut self.g.env, p);
        if le != self.tr(lhs3)? || te != self.tr(tl3)? {
            return Err("the instance is not the expected one".into())
        }
        let p = self.cast(p, tl3, tl)?;
        if lhs2 == lhs3 {
            return Ok(p)
        }
        let (t, q) = self.app_cong(lhs2, lhs3)?;
        let q = self.cast(q, t, tl)?;
        mm(self.g.lean.trans(&mut self.g.env, q, p))
    }

    /// The iota step from the closed equation `th` (`ind_iota_eq`, audit §4):
    /// `Γ ⊢ lhs2 ≡ R_c ps ms ns fs : tl`, where `lhs2` is the recursor `f` applied to `rargs`
    /// (its arguments before the major premise) and the constructor `cname` applied to
    /// `margs`. The lemma's variables are instantiated one by one from the bottom of its
    /// context (`instDF`): parameters, motives, minors, each typed at the recursor's binder,
    /// then the fields, typed along the constructor's type at the parameters of the major
    /// premise's type in the recursor's type (the recursor's own, or at an auxiliary type
    /// the nested occurrence's arguments). The instance has the constructor's own indices
    /// and those parameters and levels in the major premise: `lhs2` is equal to it by
    /// congruence. `a` is `Γ` and the levels.
    #[allow(clippy::too_many_arguments)]
    fn iota_closed(&mut self, th: mm0kit::env::ThId, fname: &str, f: ExprPtr<'t>, a: &[E], rargs: &[ExprPtr<'t>], margs: &[ExprPtr<'t>], cname: nanoda_lib::util::NamePtr<'t>, lhs2: ExprPtr<'t>, tl: ExprPtr<'t>) -> R<P> {
        let Expr::Const { name, .. } = self.read(f) else { unreachable!() };
        let rec = self.tc.env.get_recursor(&name).cloned().unwrap();
        let (np, nm, nn) = (rec.num_params as usize, rec.num_motives as usize, rec.num_minors as usize);
        let fixed = np + nm + nn;
        let Some(&crate::gen::ConstInfo { kind: crate::gen::ConstKind::Rec { i, .. }, .. }) = self.g.consts.get(fname) else { return Err("not a recursor".into()) };
        if rargs.len() < fixed || i >= nm {
            return Err("argument counts".into())
        }
        // the substitution: each argument with the type of its binder
        let mut subst = Vec::new();
        let ty = self.infer(f)?.0;
        let mut ty = crate::induct::strip_pis(self, ty);
        for (q, &x) in rargs.iter().enumerate() {
            let Expr::Pi { binder_type, body, .. } = self.read(ty) else { return Err("the recursor's type is not a telescope over its arguments".into()) };
            if q < fixed {
                subst.push((x, binder_type));
            }
            ty = self.tc.ctx.inst(body, &[x]);
        }
        let Expr::Pi { binder_type: ty_m, .. } = self.read(ty) else { return Err("the recursor's type has no binder for the major premise".into()) };
        // the constructor's parameters are those of the major premise's type: the recursor's,
        // or at an auxiliary type the nested occurrence's arguments
        let (hty, pargs) = self.tc.ctx.unfold_apps(ty_m);
        let Expr::Const { levels: mlv, .. } = self.read(hty) else { return Err("the major premise's type is not a constant's application".into()) };
        let Some(cd) = self.tc.env.get_constructor(&cname).cloned() else { return Err("unknown constructor".into()) };
        let cnp = cd.num_params as usize;
        if margs.len() < cnp || pargs.len() < cnp {
            return Err("the constructor's parameters".into())
        }
        let mut cty = crate::induct::ctor_type_at(self, &cd, mlv);
        for (q, &x) in pargs[..cnp].iter().chain(&margs[cnp..]).enumerate() {
            let Expr::Pi { binder_type, body, .. } = self.read(cty) else { return Err("the constructor's type is not a telescope over its arguments".into()) };
            if q >= cnp {
                subst.push((x, binder_type));
            }
            cty = self.tc.ctx.inst(body, &[x]);
        }
        let (_, targs) = self.tc.ctx.unfold_apps(cty);
        if targs.len() < cnp {
            return Err("the constructor's result".into())
        }
        // the instance's left-hand side and type
        let ch = self.tc.ctx.mk_const(cname, mlv);
        let major3 = self.tc.ctx.foldl_apps(ch, pargs[..cnp].iter().chain(&margs[cnp..]).copied());
        let lhs3 = self.tc.ctx.foldl_apps(f, rargs[..fixed].iter().chain(&targs[cnp..]).copied().chain([major3]));
        let tl3 = self.tc.ctx.foldl_apps(rargs[np + i], targs[cnp..].iter().copied().chain([major3]));
        let mut p = mm(self.g.env.thm(th, a, &[]))?;
        let n = subst.len();
        for (j, &(x, bt)) in subst.iter().enumerate() {
            let (tx, px) = self.infer(x)?;
            let px = self.cast(px, tx, bt)?;
            p = mm(self.g.lean.inst_df(&mut self.g.env, n - 1 - j, px, p))?;
        }
        let (_, le, _, te) = self.g.lean.deq_parts(&mut self.g.env, p);
        if le != self.tr(lhs3)? || te != self.tr(tl3)? {
            return Err("the instance is not the expected one".into())
        }
        let p = self.cast(p, tl3, tl)?;
        if lhs2 == lhs3 {
            return Ok(p)
        }
        let (t, q) = self.app_cong(lhs2, lhs3)?;
        let q = self.cast(q, t, tl)?;
        mm(self.g.lean.trans(&mut self.g.env, q, p))
    }

    /// One step at the head of `cur` (other than delta and zeta): `Γ ⊢ cur ≡ next : τ(cur)`.
    fn step_proof(&mut self, cur: ExprPtr<'t>, kind: Step) -> R<P> {
        match kind {
            Step::Proj => return self.proj_step(cur),
            Step::Quot | Step::Iota => return self.iota_step(cur, kind),
            Step::Nat => return self.nat_step(cur),
            _ => {}
        }
        if kind == Step::SortSimp {
            let Expr::Sort { level, .. } = self.read(cur) else { unreachable!() };
            let l2 = self.tc.ctx.simplify(level);
            let pl = self.level_equiv(level, l2)?;
            let (g, a, b) = (self.ctx(), self.trl(level)?, self.trl(l2)?);
            return mm(self.g.lean.sort_df(&mut self.g.env, g, a, b, pl))
        }
        let (f, args) = self.tc.ctx.unfold_apps(cur);
        let Expr::Lambda { binder_name, binder_style, binder_type, body, .. } = self.read(f) else { unreachable!() };
        let (d, g) = (self.d(), self.ctx());
        let xl = self.open(binder_name, binder_style, binder_type)?;
        let bx = self.tc.ctx.inst(body, &[xl]);
        // The reduct's head `body[a]` is a substitution instance of `bx`, and if `f` is one,
        // `bx` is one too.
        let reduct = self.tc.ctx.inst(body, &args[..1]);
        let h = Handle { src: bx, src_locals: self.locals.clone(), base: d, arg: args[0] };
        self.handles.insert((reduct, g), h);
        // abstract while the binder is still open: `abstr_levels` reads the fvar counter
        let r = self.cc("beta.body_handle", |el| el.body_handle(f, bx)).and_then(|()| self.cc(if self.tc.ctx.has_fvars(f) { "beta.body.open" } else { "beta.body.closed" }, |el| el.infer(bx))).map(|(bt, pb)| (self.tc.ctx.abstr_levels(bt, d as u16), pb));
        self.close();
        let (bt, pb) = r?;
        let (at, pa) = self.infer(args[0])?;
        let pa = self.cast(pa, at, binder_type)?;
        let mut pf = mm(self.g.lean.beta(&mut self.g.env, pb, pa))?;
        let mut ft = self.tc.ctx.inst(bt, &args[..1]);
        for &a in &args[1..] {
            (ft, pf) = self.app_step(ft, pf, a, None)?;
        }
        let tcur = self.infer(cur)?.0;
        self.cast(pf, ft, tcur)
    }
}


fn why_name(why: &DefEqWhy) -> &'static str {
    match why {
        DefEqWhy::Alpha => "defeq.alpha",
        DefEqWhy::Local => "defeq.local",
        DefEqWhy::Sort => "defeq.sort",
        DefEqWhy::Binder => "defeq.binder",
        DefEqWhy::App => "defeq.app",
        DefEqWhy::ConstApp => "defeq.const_app",
        DefEqWhy::Const => "defeq.const",
        DefEqWhy::Reduce(..) => "defeq.reduce",
        DefEqWhy::ProofIrrel => "defeq.proof_irrel",
        DefEqWhy::Eta(_) => "defeq.eta",
        DefEqWhy::Proj => "defeq.proj",
        DefEqWhy::EtaStruct => "defeq.eta_struct",
        DefEqWhy::Unit => "defeq.unit",
        DefEqWhy::NatZero => "defeq.nat_zero",
        DefEqWhy::NatSucc(..) => "defeq.nat_succ",
        DefEqWhy::StrLit => "defeq.str_lit",
        DefEqWhy::Unsupported(_) => "defeq.unsupported",
    }
}

fn step_name(kind: Step) -> &'static str {
    match kind {
        Step::Beta => "step.beta",
        Step::Zeta => "step.zeta",
        Step::Delta => "step.delta",
        Step::SortSimp => "step.sort_simp",
        Step::Proj => "step.proj",
        Step::Quot => "step.quot",
        Step::Iota => "step.iota",
        Step::Nat => "step.nat",
    }
}
