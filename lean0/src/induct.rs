//! Inductive blocks certified by the spec's schema (audit §4).
//!
//! A block becomes a data term `def X_D (us): ind = ind_mk X_blk P T` (a nested block
//! `ind_mkn X_blk P T N`: the kernel's mutual block with auxiliary types and the nested
//! occurrences `N`, from nanoda's specialization; the statements restore the occurrences),
//! and its types, constructors and recursors are the spec's `ind_ty (X_D us) i`,
//! `ind_ctor (X_D us) i c` and `ind_rec (X_D us) i v`. Their typing lemmas (`X_df`),
//! projection typing and reduction and structure eta,
//! and the iota rules (`X_rec_c_iota`) are closed equations (`iota_eq_lemma`); all are
//! theorems, proved from the schema's axioms by the Horn
//! prover over the spec: `tys_ok` (the parameters and the types' types are types),
//! `ind_wf` (the constructors are legal), `rec_ty`, `rec_rhs`, and so on. The typing facts
//! these need (each parameter, each type's type, each field's type is a type) come from the
//! elaborator, keyed by context and term for the prover's hook.
//!
//! The block's data is emitted at its first type's declaration, together with `tys_ok` and
//! the types' `_df` lemmas (whose typing needs only the earlier environment);
//! `ind_wf` is emitted at the first constructor or recursor, when the sibling types are in
//! nanoda's scope (for a nested block at the head, where the type checker is extended by
//! the block's types). The recursor's derived type and each rule's derived right-hand side
//! are compared with the export's, so the schema is checked against the kernel on every
//! block. A block the schema cannot handle (a type or constructor whose shape needs `whnf`)
//! is an error: no axioms are generated for an inductive type.
use crate::elab::{mm, Elab, R};
use crate::gen::{add_term, add_thm, apps, ConstInfo, ConstKind, Gen, Nested, Sig, StructInfo, Vars};
use crate::names::mangle;
use mm0kit::env::{Env, TermKind, ThId, TId, E, P};
use mm0kit::horn::{Hooks, Horn};
use mm0kit::lean::{Lean, View};
use mm0kit::level::Levels;
use nanoda_lib::env::{Declar, DeclarMap, InductiveData, RecursorData};
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::util::{ExprPtr, NamePtr};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::cell::Cell;
use std::rc::Rc;


/// A stage-B block.
pub struct Block {
    /// The data definition `X_D (us): ind`.
    pub data: TId,
    /// The atom `X_blk`.
    pub blk: TId,
    /// The Lean names of the declared types, in order, and of each one's constructors.
    pub names: Vec<String>,
    pub ctors: Vec<Vec<String>>,
    /// The number of types, auxiliary ones included (a nested block; audit §4).
    pub n_all: usize,
    pub nlevels: usize,
    pub lvl_names: Vec<String>,
    pub np: usize,
    pub nidx: Vec<usize>,
    /// `theorem X_D_tys: tys_ok G (X_D us)`.
    pub tys_ok: ThId,
    /// `theorem X_D_wf: ind_wf G (X_D us)`, once emitted.
    pub wf: Cell<Option<ThId>>,
}

impl Block {
    fn data_term(&self, g: &mut Gen, us: &[E]) -> E { g.env.app(self.data, us) }
}

/// Typing facts for the prover: `(context, term) → (level, proof of ty context term (srt level))`,
/// and for a constructor's result `(context, term) → proof of sty context head A term T`.
#[derive(Default)]
struct Facts {
    tys: HashMap<(E, E), (E, P)>,
    stys: HashMap<(E, E), P>,
}

impl Hooks for Facts {
    fn prove(&mut self, h: &mut Horn, env: &mut Env, lean: &mut Lean, lv: &mut Levels, goal: E) -> Option<mm0kit::env::Result<P>> {
        let (t, args) = env.head(goal)?;
        if t == env.term_id("sty") {
            let (a0, a3) = (args[0], args[3]);
            let (ctx, e) = (h.zonk(env, a0), h.zonk(env, a3));
            if !h.is_ground(env, ctx) || !h.is_ground(env, e) {
                return None
            }
            let &p = self.stys.get(&(ctx, e))?;
            let c = env.concl(p);
            return h.unify(env, goal, c).then_some(Ok(p))
        }
        if t != lean.ids.ty {
            return None
        }
        let args = args.to_vec();
        let (ctx, e) = (h.zonk(env, args[0]), h.zonk(env, args[1]));
        if !h.is_ground(env, ctx) || !h.is_ground(env, e) {
            return None
        }
        let &(l, p) = self.tys.get(&(ctx, e))?;
        // a definition of a sort (`Prop`) is read as the sort
        let want = h.zonk(env, args[2]);
        let want = env.unfold(want).unwrap_or(want);
        let sl = lean.srt(env, l);
        if h.unify(env, want, sl) {
            return Some(Ok(p))
        }
        // `ty ctx e (srt l2)` with `l ≈ l2`: cast
        let Some((ts, [l2])) = env.head(want) else { return Some(Err(mm0kit::env::Mm0Error("typing fact: not a sort".into()))) };
        if ts != lean.ids.srt {
            return Some(Err(mm0kit::env::Mm0Error("typing fact: not a sort".into())));
        }
        let l2 = *l2;
        Some((|| {
            let q = h.leqv(env, lean, lv, l, l2)?;
            let ps = lean.sort_df(env, ctx, l, l2, q)?;
            lean.defeq_df(env, ps, p)
        })())
    }
}

/// The prover and its hooks for one declaration.
struct Prover {
    horn: Horn,
    facts: Facts,
}

impl Prover {
    fn new(g: &Gen) -> Self {
        let mut horn = Horn::with_index(g.horn_index.clone());
        let mut seen = std::collections::HashSet::new();
        for b in g.blocks.values() {
            if !seen.insert(b.data) {
                continue
            }
            horn.add_clause(&g.env, b.tys_ok);
            if let Some(wf) = b.wf.get() {
                horn.add_clause(&g.env, wf);
            }
        }
        for &th in g.eeqv_axioms.values() {
            horn.add_clause(&g.env, th);
        }
        Prover { horn, facts: Facts::default() }
    }

    fn prove(&mut self, g: &mut Gen, goal: E) -> R<P> {
        mm(self.horn.prove(&mut g.env, &mut g.lean, &mut g.lv, &mut self.facts, goal))
    }

    fn apply(&mut self, g: &mut Gen, th: &str, goal: E) -> R<P> {
        let th = g.env.thm_id(th);
        mm(self.horn.apply(&mut g.env, &mut g.lean, &mut g.lv, &mut self.facts, th, goal))
    }
}

// ------------------------------------------------------------------ the declaration as data

/// The translation of a constructor or type's type body under the parameters, with the
/// block's types as variables.
struct DataTr<'t> {
    types: Vec<NamePtr<'t>>,
    uparams: Vec<NamePtr<'t>>,
}

impl<'t> DataTr<'t> {
    fn self_index(&self, el: &Elab<'_, '_, 't, '_>, e: ExprPtr<'t>) -> Option<usize> {
        let Expr::Const { name, levels, .. } = el.tc.ctx.read_expr(e) else { return None };
        let j = self.types.iter().position(|&t| t == name)?;
        let ls = el.tc.ctx.read_levels(levels);
        if ls.len() != self.uparams.len() {
            return None
        }
        for (&l, &u) in ls.iter().zip(&self.uparams) {
            match el.tc.ctx.read_level(l) {
                Level::Param(n, _) if n == u => {}
                _ => return None,
            }
        }
        Some(j)
    }

    fn has_self(&self, el: &Elab<'_, '_, 't, '_>, e: ExprPtr<'t>) -> bool {
        let mut names = Vec::new();
        el.const_names(e, &mut names);
        names.iter().any(|n| self.types.contains(n))
    }

    /// Translate `e` at depth `d` (the parameters plus the binders of `e` above it), mapping
    /// the block's types to `# (d + j)`: outside the parameters.
    fn tr(&self, el: &mut Elab<'_, '_, 't, '_>, e: ExprPtr<'t>, d: usize) -> R<E> {
        if !self.has_self(el, e) {
            return el.tr_at(e, d)
        }
        if let Some(j) = self.self_index(el, e) {
            return Ok(el.g.lean.bvar(&mut el.g.env, d + j))
        }
        match el.tc.ctx.read_expr(e) {
            Expr::App { fun, arg, .. } => {
                let (f, a) = (self.tr(el, fun, d)?, self.tr(el, arg, d)?);
                Ok(el.g.lean.app(&mut el.g.env, f, a))
            }
            Expr::Lambda { binder_type, body, .. } => {
                let (a, b) = (self.tr(el, binder_type, d)?, self.tr(el, body, d + 1)?);
                Ok(el.g.lean.lam(&mut el.g.env, a, b))
            }
            Expr::Pi { binder_type, body, .. } => {
                let (a, b) = (self.tr(el, binder_type, d)?, self.tr(el, body, d + 1)?);
                Ok(el.g.lean.pi(&mut el.g.env, a, b))
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let s = el.g.lean_name(el.tc, ty_name);
                let Some(si) = el.g.structs.get(&s) else { return Err(format!("projection of unknown structure {s}")) };
                let b = el.g.env.app(si.blk, &[]);
                let x = self.tr(el, structure, d)?;
                Ok(el.g.lean.proj(&mut el.g.env, b, idx, x))
            }
            Expr::Const { name, .. } => Err(format!("the block's type {} occurs at other levels", el.g.lean_name(el.tc, name))),
            _ => Err("the block's types occur under a let".into()),
        }
    }
}

/// The kernel's `consumeTypeAnnotations`: strip `outParam`, `semiOutParam`, `optParam` and
/// `autoParam` from the head of `e`.
pub(crate) fn consume_annots<'t>(el: &mut Elab<'_, '_, 't, '_>, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
    loop {
        let (f, args) = el.tc.ctx.unfold_apps(e);
        let Expr::Const { name, .. } = el.tc.ctx.read_expr(f) else { return e };
        let n = el.g.lean_name(el.tc, name);
        let strip = matches!((n.as_str(), args.len()), ("outParam" | "semiOutParam", 1) | ("optParam" | "autoParam", 2));
        if !strip {
            return e
        }
        e = args[0];
    }
}

/// The `Π` telescope of `ty` with each binder type's annotations consumed: the binders as
/// the kernel declares them when it builds recursors (`withLocalDecl ...
/// dom.consumeTypeAnnotations`). The block's data is stated this way, so that the derived
/// recursor types and rules are the kernel's; the types' and constructors' typing lemmas
/// state the exported (annotated) types through a definitional cast.
pub(crate) fn strip_pis<'t>(el: &mut Elab<'_, '_, 't, '_>, ty: ExprPtr<'t>) -> ExprPtr<'t> {
    match el.tc.ctx.read_expr(ty) {
        Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
            let bt = consume_annots(el, binder_type);
            let b = strip_pis(el, body);
            el.tc.ctx.mk_pi(binder_name, binder_style, bt, b)
        }
        _ => ty,
    }
}

/// A constructor's type at `levels` as the schema has it (annotations consumed; `ctor_ty`).
pub(crate) fn ctor_type_at<'t>(el: &mut Elab<'_, '_, 't, '_>, cd: &nanoda_lib::env::ConstructorData<'t>, levels: nanoda_lib::util::LevelsPtr<'t>) -> ExprPtr<'t> {
    let ty = el.tc.ctx.subst_expr_levels(cd.info.ty, cd.info.uparams, levels);
    strip_pis(el, ty)
}

/// Peel `np` parameter binders off `ty`, checking their types against `params` (translated
/// at their depth), and return the body.
fn peel_params<'t>(el: &mut Elab<'_, '_, 't, '_>, ty: ExprPtr<'t>, params: &[E]) -> R<ExprPtr<'t>> {
    let mut ty = ty;
    for (q, &p) in params.iter().enumerate() {
        let Expr::Pi { binder_type, body, .. } = el.tc.ctx.read_expr(ty) else { return Err("fewer binders than parameters".into()) };
        if el.tr_at(binder_type, q)? != p {
            return Err(format!("parameter {} differs between the block's types", q + 1))
        }
        ty = body;
    }
    Ok(ty)
}

/// The parameters of the block, from the first type's type: their translations at their
/// depths, and the context term (innermost first).
fn params<'t>(el: &mut Elab<'_, '_, 't, '_>, ty: ExprPtr<'t>, np: usize) -> R<(Vec<E>, E)> {
    let mut ps = Vec::new();
    let mut ty = ty;
    for q in 0..np {
        let Expr::Pi { binder_type, body, .. } = el.tc.ctx.read_expr(ty) else { return Err("fewer binders than parameters".into()) };
        ps.push(el.tr_at(binder_type, q)?);
        ty = body;
    }
    let mut ctx = el.g.env.app_n("nil", &[]);
    for &p in &ps {
        ctx = el.g.lean.cons(&mut el.g.env, p, ctx);
    }
    Ok((ps, ctx))
}

/// `e` is `Π ... . Sort _` with `k` binders.
fn is_sorted<'t>(el: &Elab<'_, '_, 't, '_>, mut e: ExprPtr<'t>) -> Option<usize> {
    let mut k = 0;
    loop {
        match el.tc.ctx.read_expr(e) {
            Expr::Pi { body, .. } => {
                k += 1;
                e = body
            }
            Expr::Sort { .. } => return Some(k),
            _ => return None,
        }
    }
}

// ------------------------------------------------------------------ typing facts

/// Open the binders of `ty` (at most `upto` of them) with the elaborator, recording for each
/// binder from `from` on the fact that its type is a type (in the context of the earlier
/// binders); then run `f` with them open. The binders are closed again afterwards.
fn with_binders<'t, A>(
    el: &mut Elab<'_, '_, 't, '_>, ty: ExprPtr<'t>, from: usize, upto: Option<usize>, facts: &mut Facts,
    f: impl FnOnce(&mut Elab<'_, '_, 't, '_>, ExprPtr<'t>, &mut Facts) -> R<A>,
) -> R<A> {
    let mut ty = ty;
    let mut opened = 0;
    let r = (|| {
        while let Expr::Pi { binder_name, binder_style, binder_type, body, .. } = el.tc.ctx.read_expr(ty) {
            if upto.is_some_and(|u| opened >= u) {
                break
            }
            let bt = el.inst_locals(binder_type);
            if opened >= from {
                record_type(el, bt, facts)?;
            }
            el.open_pub(binder_name, binder_style, bt)?;
            opened += 1;
            ty = body;
        }
        let body = el.inst_locals(ty);
        f(el, body, facts)
    })();
    for _ in 0..opened {
        el.close_pub();
    }
    r
}

/// Record the typing of a constructor's result `body` (with the open locals) as an `sty`
/// spine of its head at the head's type with annotations consumed, as the block's data has it
/// (`cwf_res`). An argument that does not have its binder's type leaves no fact, and the
/// schema rejects the block.
fn record_result<'t>(el: &mut Elab<'_, '_, 't, '_>, body: ExprPtr<'t>, facts: &mut Facts) -> R<()> {
    let (f, args) = el.tc.ctx.unfold_apps(body);
    let r = (|| {
        let (ty, _) = el.infer(f)?;
        let ty = strip_pis(el, ty);
        el.sty_spine_at(f, ty, &args)
    })();
    if let Ok((_, p)) = r {
        let key = (el.ctx_pub(), el.tr(body)?);
        facts.stys.insert(key, p);
    }
    Ok(())
}

/// Record that `t` (with the open locals) is a type.
fn record_type<'t>(el: &mut Elab<'_, '_, 't, '_>, t: ExprPtr<'t>, facts: &mut Facts) -> R<()> {
    let (st, p) = el.infer(t)?;
    let (level, p) = el.as_sort(p, st)?;
    let key = (el.ctx_pub(), el.tr(t)?);
    let l = el.trl(level)?;
    facts.tys.insert(key, (l, p));
    Ok(())
}

// ------------------------------------------------------------------ emission

/// The level arguments of a lemma about the block: `G` then the block's levels (var `1..`).
fn block_levels(g: &mut Gen, b: &Block) -> Vec<E> { (0..b.nlevels).map(|i| g.env.var(1 + i as u16)).collect() }

/// `theorem NAME (G) (us): concl`, proved (or stated, when replaying).
fn emit_thm(g: &mut Gen, name: &str, lvl_names: &[String], concl: E, proof: Option<P>, doc: &str) -> R<ThId> {
    let args = g.g_args(lvl_names);
    add_thm(&mut g.env, name, args, vec![], concl, false, false, proof, doc)
}

/// `X_df (G) (us) (us2): leqv us us2 > deq G (c us) (c us2) T`, the typing lemma of a block
/// constant, proved by `eeqv_df` from the schema's typing axiom and `eeqv`. `None` when
/// replaying. If `eeqv` cannot be proved (an opaque constant in the data without an `eeqv`
/// clause), the lemma is stated as an axiom and the block counted.
fn emit_df<'t>(el: &mut Elab<'_, '_, 't, '_>, pv: &mut Prover, sig: &Sig, lean_name: &str, c: E, c2: E, ty_s: ExprPtr<'t>, ty_e: ExprPtr<'t>) -> R<ThId> {
    let t = el.tr(ty_e)?;
    let ts = el.tr(ty_s)?;
    let g = &mut *el.g;
    let n = sig.lvl_names.len();
    let mut df_args = g.g_args(&sig.lvl_names);
    let lvl_s = g.env.sort_names["lvl"];
    for s in &sig.lvl_names {
        let s2 = g.var_names_fresh2(s, &sig.lvl_names);
        df_args.push((s2, lvl_s));
    }
    let gv = g.env.var(0);
    let us: Vec<E> = (0..n).map(|i| g.env.var(1 + i as u16)).collect();
    let us2: Vec<E> = (0..n).map(|i| g.env.var(1 + (n + i) as u16)).collect();
    let hyps: Vec<E> = us.iter().zip(&us2).map(|(&a, &b)| g.env.app_n("leqv", &[a, b])).collect();
    let concl = g.lean.deq(&mut g.env, gv, c, c2, t);
    let df_name = g.thms.fresh(&format!("{}_df", sig.cname));
    let doc = format!("`{lean_name}` has its type, at any equivalent levels (`constDF`).");
    if g.replay {
        return add_thm(&mut g.env, &df_name, df_args, hyps, concl, false, false, None, &doc)
    }
    pv.horn.facts.clear();
    for (i, &h) in hyps.iter().enumerate() {
        let p = g.env.hyp(i as u16, h);
        pv.horn.facts.insert(h, p);
    }
    let ty_goal = g.env.app_n("ty", &[gv, c, ts]);
    let p_ty = pv.prove(g, ty_goal).map_err(|e| format!("typing `{lean_name}` by the schema: {e}"))?;
    // the schema types the constant at the stripped type; cast to the exported one
    let p_ty = el.cast(p_ty, ty_s, ty_e)?;
    let g = &mut *el.g;
    let eq_goal = g.env.app_n("eeqv", &[c, c2]);
    match pv.prove(g, eq_goal) {
        Ok(p_eq) => {
            let th = g.env.thm_id("eeqv_df");
            let p = mm(g.env.thm(th, &[gv, c, c2, t], &[p_ty, p_eq]))?;
            add_thm(&mut g.env, &df_name, df_args, hyps, concl, false, false, Some(p), &doc)
        }
        Err(e) => Err(format!("level invariance of `{lean_name}` by the schema: {e}")),
    }
}

/// The first type of a block: emit the block's data and the types' typing lemmas, if the
/// schema handles the block; an error otherwise (the caller takes the statements back).
pub(crate) fn block_head<'t>(el: &mut Elab<'_, '_, 't, '_>, sig: &Sig, id: &InductiveData<'t>, all: &DeclarMap<'t>, nested: Option<&Nested<'t>>) -> R<()> {
    let lean_name = sig.lean_name.clone();
    let reason = |_: &mut Elab<'_, '_, 't, '_>, why: String| -> R<()> { Err(why) };
    if id.is_nested && nested.is_none() {
        return reason(el, "nested (not specialized)".into())
    }
    let uparams: Vec<NamePtr<'t>> = el.tc.ctx.read_levels(id.info.uparams).iter().map(|&l| match el.tc.ctx.read_level(l) {
        Level::Param(n, _) => n,
        _ => unreachable!(),
    }).collect();
    let np = id.num_params as usize;
    // the types of the block, from the export (the later ones are not in nanoda's scope yet):
    // each type's type, its constructors' types and its indices; for a nested block, the
    // kernel's mutual block instead (the declared types' constructors with the occurrences
    // replaced by auxiliary types, then the auxiliary types; audit §4)
    struct Header<'t> {
        name: NamePtr<'t>,
        ty: ExprPtr<'t>,
        ctors: Vec<(NamePtr<'t>, ExprPtr<'t>)>,
        nidx: usize,
    }
    let mut headers: Vec<Header<'t>> = Vec::new();
    for &n in id.all_ind_names.iter() {
        match all.get(&n) {
            Some(Declar::Inductive(d)) if d.info.uparams == id.info.uparams && d.num_params == id.num_params && d.is_nested == id.is_nested => {
                let mut ctors = Vec::new();
                for &c in d.all_ctor_names.iter() {
                    let Some(Declar::Constructor(cd)) = all.get(&c) else { return reason(el, "a constructor is missing from the export".into()) };
                    if cd.info.uparams != id.info.uparams {
                        return reason(el, "a constructor's levels differ".into())
                    }
                    ctors.push((c, cd.info.ty));
                }
                headers.push(Header { name: n, ty: d.info.ty, ctors, nidx: d.num_indices as usize });
            }
            Some(Declar::Inductive(_)) => return reason(el, "the block's types differ in parameters".into()),
            _ => return reason(el, "a type of the block is missing from the export".into()),
        }
    }
    let n0 = headers.len();
    if let Some(nst) = nested {
        let hs = &nst.st.all_inductives_incl_specialized;
        if hs.len() < n0 || hs[..n0].iter().zip(&headers).any(|(h, d)| h.name != d.name) {
            return reason(el, "the kernel's mutual block does not start with the declared types".into())
        }
        for (k, h) in hs.iter().enumerate() {
            let ctors: Vec<(NamePtr<'t>, ExprPtr<'t>)> = h.ctors.iter().map(|c| (c.name, c.ty)).collect();
            if k < n0 {
                headers[k].ctors = ctors;
            } else {
                let nidx = (el.tc.ctx.pi_telescope_size(h.ty) as usize).saturating_sub(np);
                headers.push(Header { name: h.name, ty: h.ty, ctors, nidx });
            }
        }
    }
    let names: Vec<String> = headers.iter().map(|h| el.g.lean_name(el.tc, h.name)).collect();
    let dt = DataTr { types: headers.iter().map(|h| h.name).collect(), uparams };
    // the data: parameters, each type's type and its constructors' types, with the binders'
    // annotations consumed
    let head_ty = strip_pis(el, id.info.ty);
    let (ps, pctx) = match params(el, head_ty, np) {
        Ok(x) => x,
        Err(e) => return reason(el, e),
    };
    let mut fs = Vec::new();
    let mut nidx = Vec::new();
    let mut ctor_names = Vec::new();
    let mut ks: Vec<Vec<E>> = Vec::new();
    let mut tys_s = Vec::new();
    for h in &headers {
        let dty = strip_pis(el, h.ty);
        tys_s.push(dty);
        let body = match peel_params(el, dty, &ps) {
            Ok(b) => b,
            Err(e) => return reason(el, e),
        };
        let Some(k) = is_sorted(el, body) else { return reason(el, "a type's type is not `Π indices. Sort`".into()) };
        if k != h.nidx {
            return reason(el, "index count".into())
        }
        nidx.push(k);
        fs.push(el.tr_at(body, np)?);
        let mut cs = Vec::new();
        let mut cns = Vec::new();
        for &(c, cty) in &h.ctors {
            let cty = strip_pis(el, cty);
            let body = match peel_params(el, cty, &ps) {
                Ok(b) => b,
                Err(e) => return reason(el, e),
            };
            match dt.tr(el, body, np) {
                Ok(k) => cs.push(k),
                Err(e) => return reason(el, e),
            }
            cns.push(el.g.lean_name(el.tc, c));
        }
        ks.push(cs);
        ctor_names.push(cns);
    }
    // the nested occurrences, in the data's form at depth 0 (the parameters as variables)
    let mut nctx = None;
    if let Some(nst) = nested {
        let mut xs = Vec::new();
        for (_, &e) in nst.st.nested_to_unspecialized_ty_nofvars.iter() {
            match dt.tr(el, e, np) {
                Ok(x) => xs.push(x),
                Err(e) => return reason(el, e),
            }
        }
        if n0 + xs.len() != headers.len() {
            return reason(el, "the auxiliary types and the occurrences differ in number".into())
        }
        let g = &mut *el.g;
        let mut c = g.env.app_n("nil", &[]);
        for &x in xs.iter().rev() {
            c = g.lean.cons(&mut g.env, x, c);
        }
        nctx = Some(c);
    }
    // from here on statements are emitted; a failure is rolled back by the caller
    let g = &mut *el.g;
    let n = sig.lvl_names.len();
    // the data body `ind_mk atom P T` as the definition's body (the levels are its only
    // arguments: Var(i+1) shifted to Var(i))
    let mk_body = |g: &mut Gen, atom: E| -> E {
        let mut t = g.env.app_n("tnil", &[]);
        for i in (0..fs.len()).rev() {
            let mut c = g.env.app_n("cnil", &[]);
            for &k in ks[i].iter().rev() {
                c = g.env.app_n("ccons", &[k, c]);
            }
            t = g.env.app_n("tcons", &[fs[i], c, t]);
        }
        let body = match nctx {
            Some(nc) => g.env.app_n("ind_mkn", &[atom, pctx, t, nc]),
            None => g.env.app_n("ind_mk", &[atom, pctx, t]),
        };
        let mut shift = vec![g.env.var(0)];
        shift.extend((0..n).map(|i| g.env.var(i as u16)));
        g.env.subst(body, &shift)
    };
    // Lean's `Nat` and `Eq` are the spec's blocks `nat_D` and `eq_D` (audit §4) when the
    // export declares them as the spec has them
    let spec = match lean_name.as_str() {
        "Nat" => Some(("nat_D", "nat_blk")),
        "Eq" => Some(("eq_D", "eq_blk")),
        _ => None,
    };
    let spec = spec.filter(|(d, b)| g.env.has_term(d) && g.env.has_term(b)).and_then(|(d, b)| {
        let (dt, bt) = (g.env.term_id(d), g.env.term_id(b));
        let atom = g.env.app(bt, &[]);
        let body0 = mk_body(g, atom);
        match g.env.terms[dt.0 as usize].kind {
            TermKind::Def { body, .. } if body == body0 && g.env.terms[dt.0 as usize].args.len() == n => Some((dt, bt, body0)),
            _ => None,
        }
    });
    let (data, blk, body0) = match spec {
        Some((dt, bt, body0)) => {
            g.blks.insert(lean_name.clone(), bt);
            (dt, bt, body0)
        }
        None => {
            let blk = g.blk_id(&lean_name)?;
            let atom = g.env.app(blk, &[]);
            let body0 = mk_body(g, atom);
            let data_name = g.terms.fresh(&format!("{}_D", mangle(&lean_name)));
            let ind_s = g.env.sort_names["ind"];
            let lvl_args = g.lvl_args(&sig.lvl_names);
            let data = add_term(&mut g.env, &data_name, lvl_args, ind_s, TermKind::Def { body: body0, public_body: true },
                &format!("The inductive block of `{lean_name}`: its parameters, types and constructors."))?;
            (data, blk, body0)
        }
    };
    eeqv_axioms(g, body0)?;
    let data_name = g.env.terms[data.0 as usize].name.clone();
    // theorem X_D_tys (G) (us): tys_ok G (X_D us)
    let mut pv = Prover::new(g);
    let us: Vec<E> = (0..n).map(|i| g.env.var(1 + i as u16)).collect();
    let d = g.env.app(data, &us);
    let gv = g.env.var(0);
    let goal = g.env.app_n("tys_ok", &[gv, d]);
    let proof = if g.replay {
        None
    } else {
        // the facts: each parameter type and each type's type is a type
        let mut facts = std::mem::take(&mut pv.facts);
        with_binders(el, head_ty, 0, Some(np), &mut facts, |el, _, facts| {
            for &dty in &tys_s {
                let body = peel_params(el, dty, &ps)?;
                let body = el.inst_locals(body);
                record_type(el, body, facts)?;
            }
            Ok(())
        })?;
        pv.facts = facts;
        Some(pv.prove(el.g, goal).map_err(|e| format!("the types of `{lean_name}` by the schema: {e}"))?)
    };
    let g = &mut *el.g;
    let name = g.thms.fresh(&format!("{data_name}_tys"));
    let tys_ok = emit_thm(g, &name, &sig.lvl_names, goal, proof, &format!("The parameters and types of the block of `{lean_name}` are types."))?;
    let names: Vec<String> = names[..n0].to_vec();
    let block = Rc::new(Block {
        data,
        blk,
        names: names.clone(),
        ctors: ctor_names[..n0].to_vec(),
        n_all: headers.len(),
        nlevels: n,
        lvl_names: sig.lvl_names.clone(),
        np,
        nidx,
        tys_ok,
        wf: Cell::new(None),
    });
    pv.horn.add_clause(&g.env, tys_ok);
    for n in &names {
        g.blocks.insert(n.clone(), block.clone());
    }
    // each type's typing lemma (an auxiliary type's too: the specialized constructors mention it)
    for (i, h) in headers.iter().enumerate() {
        let tname = el.g.lean_name(el.tc, h.name);
        let cname = if i == 0 { sig.cname.clone() } else { el.g.terms.fresh(&mangle(&tname)) };
        let tsig = Sig { lean_name: tname.clone(), cname, lvl_names: sig.lvl_names.clone() };
        el.g.consts.insert(tname.clone(), ConstInfo { term: data, kind: ConstKind::Ind { i }, nlevels: n, ty_thm: ThId(0) });
        let g = &mut *el.g;
        let us2: Vec<E> = (0..n).map(|i| g.env.var(1 + (n + i) as u16)).collect();
        let c = g.const_term(&tname, &us).unwrap();
        let c2 = g.const_term(&tname, &us2).unwrap();
        let df = emit_df(el, &mut pv, &tsig, &tname, c, c2, tys_s[i], h.ty)?;
        el.g.consts.get_mut(&tname).unwrap().ty_thm = df;
    }
    // a nested block is checked here, where its types are all in the type checker's scope
    // (through the temporary declarations)
    if nested.is_some() {
        ensure_wf(el, &mut pv, &block, id.info.name, all, nested)?;
    }
    el.g.stage_b += 1;
    Ok(())
}

/// Level congruence of the opaque constants in the block's data. `eeqv (c us) (c us2)` has
/// no clause when `c` is a generated term that is not a public definition (an opaque, an
/// axiom, a theorem), so a block whose data mentions one at its levels
/// gets `axiom c_eeqv (us us2): leqv u u2 > ... > eeqv (c us) (c us2)`, once per constant
/// (audit §4; `lean0 check` checks the shape). The scan mirrors the prover: a subterm
/// without level variables is `eeqv_refl`, a public definition is unfolded.
fn eeqv_axioms(g: &mut Gen, data: E) -> R<()> {
    let mut marked = Vec::new();
    scan_eeqv(g, data, &mut HashSet::default(), &mut HashMap::default(), &mut marked);
    for t in marked {
        if g.eeqv_axioms.contains_key(&t) {
            continue
        }
        let d = g.env.terms[t.0 as usize].clone();
        let lean = g.consts.iter().find(|(_, ci)| ci.term == t).map(|(n, _)| n.clone()).unwrap_or_else(|| d.name.clone());
        let n = d.args.len();
        let lvl_names: Vec<String> = d.args.iter().map(|a| a.0.clone()).collect();
        let mut args = g.lvl_args(&lvl_names);
        let lvl_s = g.env.sort_names["lvl"];
        for s in &lvl_names {
            let s2 = g.var_names_fresh2(s, &lvl_names);
            args.push((s2, lvl_s));
        }
        let us: Vec<E> = (0..n).map(|i| g.env.var(i as u16)).collect();
        let us2: Vec<E> = (0..n).map(|i| g.env.var((n + i) as u16)).collect();
        let hyps: Vec<E> = us.iter().zip(&us2).map(|(&a, &b)| g.env.app_n("leqv", &[a, b])).collect();
        let (c1, c2) = (g.env.app(t, &us), g.env.app(t, &us2));
        let concl = g.env.app_n("eeqv", &[c1, c2]);
        let name = g.thms.fresh(&format!("{}_eeqv", d.name));
        let th = add_thm(&mut g.env, &name, args, hyps, concl, true, false, None,
            &format!("`{lean}` at equivalent levels is the same expression up to levels (an opaque constant in an inductive declaration)."))?;
        g.eeqv_axioms.insert(t, th);
    }
    Ok(())
}

/// The generated terms of `e` whose level congruence the prover needs (`eeqv_axioms`).
fn scan_eeqv(g: &mut Gen, e: E, seen: &mut HashSet<E>, lvars: &mut HashMap<E, bool>, marked: &mut Vec<TId>) {
    if !seen.insert(e) || !has_var(&g.env, e, lvars) {
        return
    }
    let Some((t, args)) = g.env.head(e) else { return };
    let args = args.to_vec();
    if (t.0 as usize) < g.spec_terms {
        for a in args {
            scan_eeqv(g, a, seen, lvars, marked);
        }
    } else if matches!(g.env.terms[t.0 as usize].kind, TermKind::Def { public_body: true, .. }) {
        let e2 = g.env.unfold(e).unwrap();
        scan_eeqv(g, e2, seen, lvars, marked);
    } else if !marked.contains(&t) {
        marked.push(t);
    }
}

/// `e` mentions a statement variable (a level, in a block's data).
fn has_var(env: &Env, e: E, memo: &mut HashMap<E, bool>) -> bool {
    if let Some(&b) = memo.get(&e) {
        return b
    }
    let b = match env.node(e) {
        mm0kit::env::Node::Var(_) => true,
        mm0kit::env::Node::Meta(_) => false,
        mm0kit::env::Node::App(_, xs) => {
            let xs = xs.to_vec();
            xs.iter().any(|&x| has_var(env, x, memo))
        }
    };
    memo.insert(e, b);
    b
}

/// Emit `theorem X_D_wf: ind_wf G (X_D us)` if it is not yet (the sibling types must be in
/// nanoda's scope: at a constructor or recursor).
fn ensure_wf<'t>(el: &mut Elab<'_, '_, 't, '_>, pv: &mut Prover, block: &Rc<Block>, ind: NamePtr<'t>, all: &DeclarMap<'t>, nested: Option<&Nested<'t>>) -> R<ThId> {
    if let Some(wf) = block.wf.get() {
        return Ok(wf)
    }
    let g = &mut *el.g;
    let us = block_levels(g, block);
    let d = block.data_term(g, &us);
    let gv = g.env.var(0);
    let goal = g.env.app_n("ind_wf", &[gv, d]);
    let proof = if g.replay {
        None
    } else {
        let mut facts = std::mem::take(&mut pv.facts);
        ctor_facts(el, ind, block.np, all, &mut facts, nested)?;
        pv.facts = facts;
        Some(pv.prove(el.g, goal).map_err(|e| format!("the constructors of `{}` by the schema: {e}", block.names[0]))?)
    };
    let g = &mut *el.g;
    let data_name = g.env.terms[block.data.0 as usize].name.clone();
    let name = g.thms.fresh(&format!("{data_name}_wf"));
    let wf = emit_thm(g, &name, &block.lvl_names, goal, proof, &format!("The block of `{}` is a legal inductive declaration.", block.names[0]))?;
    block.wf.set(Some(wf));
    pv.horn.add_clause(&g.env, wf);
    Ok(wf)
}

/// The facts for every field of every constructor of the block (`ind_wf`, `elim_ok`,
/// `proj_ok`); `ind` is any type of the block, which must be in nanoda's scope. For a nested
/// block, the constructors of the kernel's mutual block (the auxiliary types are in scope
/// through the temporary declarations).
fn ctor_facts<'t>(el: &mut Elab<'_, '_, 't, '_>, ind: NamePtr<'t>, np: usize, all: &DeclarMap<'t>, facts: &mut Facts, nested: Option<&Nested<'t>>) -> R<()> {
    if let Some(nst) = nested {
        for h in &nst.st.all_inductives_incl_specialized {
            for c in &h.ctors {
                let ty = strip_pis(el, c.ty);
                with_binders(el, ty, np, None, facts, record_result)?;
            }
        }
        // each occurrence's arguments, under the parameters (`nst_ty`)
        if let Some(h) = nst.st.all_inductives_incl_specialized.first() {
            let ty = strip_pis(el, h.ty);
            let occs: Vec<ExprPtr<'t>> = nst.st.nested_to_unspecialized_ty_nofvars.values().copied().collect();
            with_binders(el, ty, np, Some(np), facts, |el, _, facts| {
                for &x in &occs {
                    let x = el.inst_locals(x);
                    record_result(el, x, facts)?;
                }
                Ok(())
            })?;
        }
        return Ok(())
    }
    let Some(Declar::Inductive(id)) = all.get(&ind) else { return Err("the block's types are not in the export".into()) };
    for &t in id.all_ind_names.iter() {
        let Some(Declar::Inductive(d)) = all.get(&t) else { return Err("a type of the block is not in the export".into()) };
        for &c in d.all_ctor_names.iter() {
            let Some(Declar::Constructor(cd)) = all.get(&c) else { return Err("a constructor of the block is not in the export".into()) };
            let ty = strip_pis(el, cd.info.ty);
            with_binders(el, ty, np, None, facts, record_result)?;
        }
    }
    Ok(())
}

/// A constructor of a stage-B block: its typing lemma, and for a structure the projection
/// and eta lemmas. `Ok(false)`: not a stage-B block.
pub(crate) fn constructor<'t>(el: &mut Elab<'_, '_, 't, '_>, sig: &Sig, cd: &nanoda_lib::env::ConstructorData<'t>, all: &DeclarMap<'t>, nested: Option<&Nested<'t>>) -> R<bool> {
    let ind = el.g.lean_name(el.tc, cd.inductive_name);
    let Some(block) = el.g.blocks.get(&ind).cloned() else { return Ok(false) };
    let i = block.names.iter().position(|n| *n == ind).unwrap();
    let c = cd.ctor_idx as usize;
    let mut pv = Prover::new(el.g);
    ensure_wf(el, &mut pv, &block, cd.inductive_name, all, nested)?;
    let n = block.nlevels;
    el.g.consts.insert(sig.lean_name.clone(), ConstInfo { term: block.data, kind: ConstKind::Ctor { i, c }, nlevels: n, ty_thm: ThId(0) });
    let ty_s = strip_pis(el, cd.info.ty);
    let g = &mut *el.g;
    let us = block_levels(g, &block);
    let us2: Vec<E> = (0..n).map(|i| g.env.var(1 + (n + i) as u16)).collect();
    let ct = g.const_term(&sig.lean_name, &us).unwrap();
    let ct2 = g.const_term(&sig.lean_name, &us2).unwrap();
    let df = emit_df(el, &mut pv, sig, &sig.lean_name, ct, ct2, ty_s, cd.info.ty)?;
    el.g.consts.get_mut(&sig.lean_name).unwrap().ty_thm = df;
    if el.tc.env.get_structure(&cd.inductive_name, true).is_some() {
        // the field types as the schema has them (annotations consumed); a projection's use
        // casts to nanoda's type (`Elab::proj_cast`)
        let fields = crate::gen::structure_fields(el, cd.inductive_name, ty_s)?;
        structure(el, &mut pv, sig, &block, i, cd, fields)?;
    }
    Ok(true)
}

/// Projections of a structure `S` (one constructor, no indices): per field `i` a typing
/// lemma and a reduction lemma, plus structure eta when `S` is not recursive, proved from
/// `proj_ty`, `proj_mk` and `ind_eta`.
///
/// The typing lemma substitutes the parameters and the earlier projections into the field
/// type through `inst` premises, outermost first (the spec's `pinst` and `qinst`). When `S`
/// may live in `Prop`, a field that is not a proposition (or follows one that is not) may
/// only be projected from a structure whose sort is at least 1, so its lemma takes the
/// premise `leqv (lmax (ls lz) L) L` (as nanoda's `infer_proj` checks). If the fields up to
/// it are propositions at some levels only, a second lemma (`_dfp`) puts their sort levels
/// at `lz`.
fn structure<'t>(el: &mut Elab<'_, '_, 't, '_>, pv: &mut Prover, sig: &Sig, block: &Rc<Block>, j: usize, cd: &nanoda_lib::env::ConstructorData<'t>, fields: crate::gen::Fields) -> R<()> {
    let ind_lean = block.names[j].clone();
    let eta_ok = el.tc.env.can_be_struct(&cd.inductive_name);
    let np = block.np;
    let crate::gen::Fields { tys: field_tys, is_prop, levels: field_lvls, sort: lsort } = fields;
    let nf = field_tys.len();
    // the facts: the fields' types (`proj_ok_prop`)
    let ty_s = strip_pis(el, cd.info.ty);
    if !el.g.replay {
        let mut facts = std::mem::take(&mut pv.facts);
        with_binders(el, ty_s, np, None, &mut facts, |_, _, _| Ok(()))?;
        pv.facts = facts;
    }
    let g = &mut *el.g;
    let sort_ok = !crate::gen::level_may_be_zero(g, lsort);
    let blk = block.blk;
    let proj = g.env.app(blk, &[]);
    let proj_name = format!("{}_proj", mangle(&ind_lean));
    let mut df = Vec::new();
    let mut df_prop = Vec::new();
    for i in 0..nf {
        let needs_sort = !sort_ok && !is_prop[..=i].iter().all(|&b| b);
        let lvl_js: Vec<usize> = (0..=i).filter(|&j| !is_prop[j]).collect();
        let prop_ok = needs_sort && lvl_js.iter().all(|&j| crate::gen::level_may_be_zero(g, field_lvls[j]));
        let mut variants = vec![needs_sort];
        if prop_ok {
            variants.push(false);
        }
        for (vi, &sort_premise) in variants.iter().enumerate() {
            let from_prop = vi == 1;
            let mut v = Vars::new();
            let gv = v.add(&mut g.env, "G", "ctx");
            let us = v.lvls(&mut g.env, &sig.lvl_names, "");
            let ps = v.many(&mut g.env, "p", "expr", np);
            let (e, e2) = (v.add(&mut g.env, "e", "expr"), v.add(&mut g.env, "e2", "expr"));
            let mut hyps = Vec::new();
            let subst: Vec<E> = std::iter::once(gv).chain(us.iter().copied()).collect();
            let lsort_here = g.env.subst(lsort, &subst);
            if sort_premise {
                let z = g.env.app_n("lz", &[]);
                let one = g.env.app_n("ls", &[z]);
                let m = g.env.app_n("lmax", &[one, lsort_here]);
                hyps.push(g.env.app_n("leqv", &[m, lsort_here]));
            }
            if from_prop {
                let z = g.env.app_n("lz", &[]);
                for &j in &lvl_js {
                    let l = g.env.subst(field_lvls[j], &subst);
                    hyps.push(g.env.app_n("leqv", &[l, z]));
                }
            }
            let st = g.const_term(&ind_lean, &us).unwrap();
            let st = apps(g, st, &ps);
            hyps.push(g.lean.deq(&mut g.env, gv, e, e2, st));
            let (ihyps, r) = crate::gen::field_inst_hyps(g, &mut v, field_tys[i], &subst, &ps, i, proj, e);
            hyps.extend(ihyps);
            let (pe, pe2) = (g.lean.proj(&mut g.env, proj, i, e), g.lean.proj(&mut g.env, proj, i, e2));
            let concl = g.lean.deq(&mut g.env, gv, pe, pe2, r);
            let name = g.thms.fresh(&format!("{proj_name}_{i}_df{}", if from_prop { "p" } else { "" }));
            let what = if from_prop {
                " (from a proposition, when the fields up to it are propositions)"
            } else if sort_premise {
                " (not from a proposition)"
            } else {
                ""
            };
            let proof = prove_lemma(g, pv, "proj_ty", &hyps, concl)?;
            let th = add_thm(&mut g.env, &name, v.args, hyps, concl, false, false, proof, &format!("Typing of field {i} of `{ind_lean}`{what}."))?;
            if from_prop {
                df_prop.push(Some((th, lvl_js.iter().map(|&j| field_lvls[j]).collect())));
            } else {
                df.push((th, needs_sort));
            }
        }
        if !prop_ok {
            df_prop.push(None);
        }
    }
    let mut red = Vec::new();
    let mut red_prop = Vec::new();
    for i in 0..nf {
        // `proj_ok`'s premises, as the typing lemmas'
        let needs_sort = !sort_ok && !is_prop[..=i].iter().all(|&b| b);
        let lvl_js: Vec<usize> = (0..=i).filter(|&j| !is_prop[j]).collect();
        let prop_ok = needs_sort && lvl_js.iter().all(|&j| crate::gen::level_may_be_zero(g, field_lvls[j]));
        let mut variants = vec![needs_sort];
        if prop_ok {
            variants.push(false);
        }
        for (vi, &sort_premise) in variants.iter().enumerate() {
            let from_prop = vi == 1;
            let mut v = Vars::new();
            let gv = v.add(&mut g.env, "G", "ctx");
            let cls = v.lvls(&mut g.env, &sig.lvl_names, "");
            let mut hyps = Vec::new();
            let subst: Vec<E> = std::iter::once(gv).chain(cls.iter().copied()).collect();
            let z = g.env.app_n("lz", &[]);
            if sort_premise {
                let lsort_here = g.env.subst(lsort, &subst);
                let one = g.env.app_n("ls", &[z]);
                let m = g.env.app_n("lmax", &[one, lsort_here]);
                hyps.push(g.env.app_n("leqv", &[m, lsort_here]));
            }
            if from_prop {
                for &j in &lvl_js {
                    let l = g.env.subst(field_lvls[j], &subst);
                    hyps.push(g.env.app_n("leqv", &[l, z]));
                }
            }
            let c = g.const_term(&sig.lean_name, &cls).unwrap();
            let name = g.thms.fresh(&format!("{proj_name}_{i}_mk{}", if from_prop { "p" } else { "" }));
            let th = proj_eq_lemma(g, pv, v.args, hyps, &name, c, i, block.wf.get(), &cls, &format!("Field {i} of a `{}` application, as a closed equation.", sig.lean_name))?;
            if from_prop {
                red_prop.push(Some(th));
            } else {
                red.push((th, needs_sort));
            }
        }
        if !prop_ok {
            red_prop.push(None);
        }
    }
    let eta = if eta_ok {
        let mut v = Vars::new();
        let gv = v.add(&mut g.env, "G", "ctx");
        let us = v.lvls(&mut g.env, &sig.lvl_names, "");
        let ps = v.many(&mut g.env, "p", "expr", np);
        let e = v.add(&mut g.env, "e", "expr");
        let st = g.const_term(&ind_lean, &us).unwrap();
        let st = apps(g, st, &ps);
        let hyp = g.env.app_n("ty", &[gv, e, st]);
        let projs: Vec<E> = (0..nf).map(|i| g.lean.proj(&mut g.env, proj, i, e)).collect();
        let m = g.const_term(&sig.lean_name, &us).unwrap();
        let m = apps(g, m, &[ps, projs].concat());
        let concl = g.lean.deq(&mut g.env, gv, e, m, st);
        let name = g.thms.fresh(&format!("{}_eta", mangle(&ind_lean)));
        let proof = prove_lemma(g, pv, "ind_eta", &[hyp], concl)?;
        Some(add_thm(&mut g.env, &name, v.args, vec![hyp], concl, false, false, proof, &format!("Structure eta for `{ind_lean}`."))?)
    } else {
        None
    };
    g.structs.insert(ind_lean, StructInfo { blk, np, nf, df, df_prop, red, red_prop, eta, sort: lsort, field_tys });
    Ok(())
}

/// Prove `concl` from `hyps` by the schema axiom `rule` (`None` when replaying).
fn prove_lemma(g: &mut Gen, pv: &mut Prover, rule: &str, hyps: &[E], concl: E) -> R<Option<P>> {
    if g.replay {
        return Ok(None)
    }
    pv.horn.facts.clear();
    for (i, &h) in hyps.iter().enumerate() {
        let p = g.env.hyp(i as u16, h);
        pv.horn.facts.insert(h, p);
    }
    Ok(Some(pv.apply(g, rule, concl)?))
}

/// The arguments of an application spine, first to last.
fn spine_args(g: &Gen, mut e: E) -> Vec<E> {
    let mut out = Vec::new();
    while let View::App(f, a) = g.lean.view(&g.env, e) {
        out.push(a);
        e = f;
    }
    out.reverse();
    out
}

/// Iota as a closed equation (`ind_iota_eq`, audit §4), for the recursor `rt` (`ind_rec D i v`)
/// on its type's constructor number `c`:
/// `⟦ Dl ++ G ⊢ rec ps ms ns is (ctor ps fs) ≡ def ps ms ns fs : motive is (ctor ps fs) ⟧`
/// (at an auxiliary type the constructor is the nested block's, at the occurrence's arguments),
/// every argument a variable of the rule's context `Dl` (the fields over the minors, the
/// motives and the parameters) or an index of the constructor's result, over any base
/// context `G` (`weakBaseDF`), with the block's nested occurrences restored. The statement
/// comes from Part I's `iota_eq`, `crst` and `rst` alone, so a replayed declaration states
/// it without the proof.
#[allow(clippy::too_many_arguments)]
fn iota_eq_lemma(g: &mut Gen, pv: &mut Prover, args: Vec<(String, u8)>, name: &str, rt: E, c: E, def_us: E, fixed: usize, nf: usize, wf: (ThId, &[E]), elim: Option<ThId>, doc: &str) -> R<ThId> {
    let (d, i, v) = match g.env.head(rt) {
        Some((_, &[d, i, v])) => (d, i, v),
        _ => return Err("not a recursor term".into()),
    };
    pv.horn.facts.clear();
    // the rule's context, sides and type: Part I's `iota_eq`
    let p_eq = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 4, |env, ms| env.app_n("iota_eq", &[d, i, c, v, ms[0], ms[1], ms[2], ms[3]])))?;
    let c_eq = g.env.concl(p_eq);
    let (dl0, lhs0, rhs0, ty0) = g.env.head(c_eq).map(|(_, a)| (a[4], a[5], a[6], a[7])).ok_or("iota_eq")?;
    // restored to the block's nested occurrences (nothing for a block without them)
    let p_n = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 1, |env, ms| env.app_n("ind_nested", &[d, ms[0]])))?;
    let c_n = g.env.concl(p_n);
    let n = g.env.head(c_n).map(|(_, a)| a[1]).ok_or("ind_nested")?;
    let mut restored = Vec::new();
    for (rel, e) in [("crst", dl0), ("rst", lhs0), ("rst", rhs0), ("rst", ty0)] {
        let p = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 1, |env, ms| env.app_n(rel, &[d, n, e, ms[0]])))?;
        let cp = g.env.concl(p);
        let e2 = g.env.head(cp).map(|(_, a)| a[3]).ok_or("rst")?;
        restored.push((cp, p, e2));
    }
    let (dl, lhs, rhs_u, ty) = (restored[0].2, restored[1].2, restored[2].2, restored[3].2);
    // the right-hand side through the rule's definition: its arguments are the recursor's
    // before the indices, then the fields
    let View::App(e4, maj) = g.lean.view(&g.env, lhs) else { return Err("iota_eq: the left-hand side".into()) };
    let mut ra = spine_args(g, e4);
    let ma = spine_args(g, maj);
    if ma.len() < nf || ra.len() < fixed {
        return Err("iota_eq: too few arguments".into())
    }
    ra.truncate(fixed);
    ra.extend(&ma[ma.len() - nf..]);
    let rhs = crate::gen::apps(g, def_us, &ra);
    // the context over the base `G`
    let mut entries = Vec::new();
    let mut t = dl;
    while let Some((h, &[a, rest])) = g.env.head(t) {
        if h != g.lean.ids.cons {
            break
        }
        entries.push(a);
        t = rest;
    }
    let mut dlg = g.env.var(0);
    for &a in entries.iter().rev() {
        dlg = g.lean.cons(&mut g.env, a, dlg);
    }
    let concl = g.lean.deq(&mut g.env, dlg, lhs, rhs, ty);
    let proof = if g.replay {
        None
    } else {
        pv.horn.facts.insert(c_eq, p_eq);
        pv.horn.facts.insert(c_n, p_n);
        for &(cp, p, _) in &restored {
            pv.horn.facts.insert(cp, p);
        }
        if let Some(th) = elim {
            // `elim_ok` at the rule's context, from the recursor's lemma over any context
            let mut la = vec![dl];
            la.extend((1..args.len()).map(|k| g.env.var(k as u16)));
            let q = mm(g.env.thm(th, &la, &[]))?;
            let cq = g.env.concl(q);
            pv.horn.facts.insert(cq, q);
        }
        // the block is read off `ind_wf`, the rule's first premise: the block's lemma at the
        // rule's context
        let mut wa = vec![dl];
        wa.extend(wf.1);
        let p_wf = mm(g.env.thm(wf.0, &wa, &[]))?;
        let c_wf = g.env.concl(p_wf);
        pv.horn.facts.insert(c_wf, p_wf);
        let goal_u = g.lean.deq(&mut g.env, dl, lhs, rhs_u, ty);
        let p0 = pv.apply(g, "ind_iota_eq", goal_u)?;
        let goal0 = g.lean.deq(&mut g.env, dl, lhs, rhs, ty);
        let p0 = mm(g.env.convert(p0, goal0))?;
        pv.horn.facts.clear();
        pv.horn.facts.insert(goal0, p0);
        let p = pv.apply(g, "weakBaseDF", concl)?;
        pv.horn.facts.clear();
        Some(p)
    };
    add_thm(&mut g.env, name, args, Vec::new(), concl, false, false, proof, doc)
}

/// The projection rule as a closed equation (`proj_mk`, audit §4): field `i` of the
/// constructor `c` (`ind_ctor D j 0`) applied to the variables of the rule's context `Dl`
/// (the fields over the parameters) is the field's variable, over any base context `G`
/// (`weakBaseDF`), with the block's nested occurrences restored, under the hypotheses `hyps`
/// of `proj_ok` (on the levels). The statement comes from Part I's `proj_eq`, `crst`, `rst`
/// and `lookup` alone, so a replayed declaration states it without the proof.
#[allow(clippy::too_many_arguments)]
fn proj_eq_lemma(g: &mut Gen, pv: &mut Prover, args: Vec<(String, u8)>, hyps: Vec<E>, name: &str, c: E, i: usize, wf: Option<ThId>, us: &[E], doc: &str) -> R<ThId> {
    let (d, j) = match g.env.head(c) {
        Some((_, &[d, j, _])) => (d, j),
        _ => return Err("not a constructor term".into()),
    };
    pv.horn.facts.clear();
    let ie = g.lean.nat(&mut g.env, i);
    let p_eq = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 3, |env, ms| env.app_n("proj_eq", &[d, j, ie, ms[0], ms[1], ms[2]])))?;
    let c_eq = g.env.concl(p_eq);
    let (dl0, lhs0, k) = g.env.head(c_eq).map(|(_, a)| (a[3], a[4], a[5])).ok_or("proj_eq")?;
    let p_n = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 1, |env, ms| env.app_n("ind_nested", &[d, ms[0]])))?;
    let c_n = g.env.concl(p_n);
    let n = g.env.head(c_n).map(|(_, a)| a[1]).ok_or("ind_nested")?;
    let mut restored = Vec::new();
    for (rel, e) in [("crst", dl0), ("rst", lhs0)] {
        let p = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 1, |env, ms| env.app_n(rel, &[d, n, e, ms[0]])))?;
        let cp = g.env.concl(p);
        let e2 = g.env.head(cp).map(|(_, a)| a[3]).ok_or("rst")?;
        restored.push((cp, p, e2));
    }
    let (dl, lhs) = (restored[0].2, restored[1].2);
    let p_lk = mm(pv.horn.prove_open(&mut g.env, &mut g.lean, &mut g.lv, &mut pv.facts, 1, |env, ms| env.app_n("lookup", &[dl, k, ms[0]])))?;
    let c_lk = g.env.concl(p_lk);
    let ty = g.env.head(c_lk).map(|(_, a)| a[2]).ok_or("lookup")?;
    let rhs = g.env.app_n("bvar", &[k]);
    // the context over the base `G`
    let mut entries = Vec::new();
    let mut t = dl;
    while let Some((h, &[a, rest])) = g.env.head(t) {
        if h != g.lean.ids.cons {
            break
        }
        entries.push(a);
        t = rest;
    }
    let mut dlg = g.env.var(0);
    for &a in entries.iter().rev() {
        dlg = g.lean.cons(&mut g.env, a, dlg);
    }
    let concl = g.lean.deq(&mut g.env, dlg, lhs, rhs, ty);
    let proof = if g.replay {
        None
    } else {
        // `proj_ok` over any context, from the hypotheses: a lemma, used at the rule's context
        // (the typing facts are those of the declaration's context)
        let g0 = g.env.var(0);
        let ok_goal = g.env.app_n("proj_ok", &[g0, d, j, ie]);
        pv.horn.facts.clear();
        for (q, &h) in hyps.iter().enumerate() {
            let p = g.env.hyp(q as u16, h);
            pv.horn.facts.insert(h, p);
        }
        let p_ok = pv.prove(g, ok_goal)?;
        let mut ok_name = format!("{}{name}_ok", mm0kit::lean::FACT_PREFIX);
        while g.env.has_thm(&ok_name) {
            ok_name.push('_');
        }
        let ok = add_thm(&mut g.env, &ok_name, args.clone(), hyps.clone(), ok_goal, false, true, Some(p_ok), "")?;
        let hp: Vec<P> = hyps.iter().enumerate().map(|(q, &h)| g.env.hyp(q as u16, h)).collect();
        let mut la = vec![dl];
        la.extend(us);
        let q_ok = mm(g.env.thm(ok, &la, &hp))?;
        let Some(wf) = wf else { return Err("the block's well-formedness lemma is missing".into()) };
        let q_wf = mm(g.env.thm(wf, &la, &[]))?;
        pv.horn.facts.clear();
        for q in [q_ok, q_wf, p_eq, p_n, restored[0].1, restored[1].1, p_lk] {
            let cq = g.env.concl(q);
            pv.horn.facts.insert(cq, q);
        }
        let goal0 = g.lean.deq(&mut g.env, dl, lhs, rhs, ty);
        let p0 = pv.apply(g, "proj_mk", goal0)?;
        pv.horn.facts.clear();
        pv.horn.facts.insert(goal0, p0);
        let p = pv.apply(g, "weakBaseDF", concl)?;
        pv.horn.facts.clear();
        Some(p)
    };
    add_thm(&mut g.env, name, args, hyps, concl, false, false, proof, doc)
}

/// The spec's closed equation `ax` at the levels `us` (a rule without premises whose context
/// is closed: `quot_lift_mk`), over any base context `G` (`weakBaseDF`): the
/// theorem `name` over `args` (`G`, then the levels).
pub(crate) fn closed_over_base(g: &mut Gen, ax: &str, us: &[E], name: &str, args: Vec<(String, u8)>, doc: &str) -> R<ThId> {
    let th = g.env.thm_id(ax);
    let c0 = g.env.plain_concl(th);
    let c0 = g.env.subst(c0, us);
    let Some((_, &[dl, lhs, rhs, ty])) = g.env.head(c0) else { return Err(format!("{ax}: not an equation")) };
    let mut entries = Vec::new();
    let mut t = dl;
    while let Some((h, &[a, rest])) = g.env.head(t) {
        if h != g.lean.ids.cons {
            break
        }
        entries.push(a);
        t = rest;
    }
    let mut dlg = g.env.var(0);
    for &a in entries.iter().rev() {
        dlg = g.lean.cons(&mut g.env, a, dlg);
    }
    let concl = g.lean.deq(&mut g.env, dlg, lhs, rhs, ty);
    let proof = if g.replay {
        None
    } else {
        let p0 = mm(g.env.thm(th, us, &[]))?;
        let p0 = mm(g.env.convert(p0, c0))?;
        let mut pv = Prover::new(g);
        pv.horn.facts.insert(c0, p0);
        Some(pv.apply(g, "weakBaseDF", concl)?)
    };
    add_thm(&mut g.env, name, args, Vec::new(), concl, false, false, proof, doc)
}

/// The type whose recursor `name` is: `X.rec` for a declared type `X`, or `X.rec_k` (`X` the
/// first type) for the `k`th auxiliary type of a nested block (`mkAuxRecNameMap`).
fn rec_index(block: &Block, name: &str) -> Option<usize> {
    if let Some(i) = block.names.iter().position(|n| format!("{n}.rec") == name) {
        return Some(i)
    }
    let k: usize = name.strip_prefix(&format!("{}.rec_", block.names[0]))?.parse().ok()?;
    let i = block.names.len() + k.checked_sub(1)?;
    (i < block.n_all).then_some(i)
}

/// A recursor of a stage-B block: its typing lemma and its rules' definitions and iota
/// lemmas. `Ok(false)`: not a stage-B block.
pub(crate) fn recursor<'t>(el: &mut Elab<'_, '_, 't, '_>, sig: &Sig, rd: &RecursorData<'t>, all: &DeclarMap<'t>, nested: Option<&Nested<'t>>) -> R<bool> {
    let Some(&ind_name) = rd.all_inductives.first() else { return Ok(false) };
    let ind = el.g.lean_name(el.tc, ind_name);
    let Some(block) = el.g.blocks.get(&ind).cloned() else { return Ok(false) };
    let rec_all: Vec<String> = rd.all_inductives.iter().map(|&n| el.g.lean_name(el.tc, n)).collect();
    if rec_all != block.names {
        return Ok(false)
    }
    let Some(i) = rec_index(&block, &sig.lean_name) else { return Ok(false) };
    let nl = el.tc.ctx.read_levels(rd.info.uparams).len();
    let large = nl == block.nlevels + 1;
    if !large && nl != block.nlevels {
        return Err("recursor levels".into())
    }
    let mut pv = Prover::new(el.g);
    let wf = ensure_wf(el, &mut pv, &block, ind_name, all, nested)?;
    if !el.g.replay {
        // `elim_ok` may need the fields' types (one constructor whose fields are propositions)
        let mut facts = std::mem::take(&mut pv.facts);
        ctor_facts(el, ind_name, block.np, all, &mut facts, nested)?;
        pv.facts = facts;
    }
    el.g.consts.insert(sig.lean_name.clone(), ConstInfo { term: block.data, kind: ConstKind::Rec { i, large }, nlevels: nl, ty_thm: ThId(0) });
    let g = &mut *el.g;
    let us: Vec<E> = (0..nl).map(|i| g.env.var(1 + i as u16)).collect();
    let us2: Vec<E> = (0..nl).map(|i| g.env.var(1 + (nl + i) as u16)).collect();
    let rt = g.const_term(&sig.lean_name, &us).unwrap();
    let rt2 = g.const_term(&sig.lean_name, &us2).unwrap();
    let df = emit_df(el, &mut pv, sig, &sig.lean_name, rt, rt2, rd.info.ty, rd.info.ty)?;
    el.g.consts.get_mut(&sig.lean_name).unwrap().ty_thm = df;
    // the rules mention the sibling recursors of a mutual block, declared later: register
    // them now (their own declaration sets their typing lemma)
    for r in rd.rec_rules.iter() {
        let mut names = Vec::new();
        el.const_names(r.val, &mut names);
        for n in names {
            let c = el.g.lean_name(el.tc, n);
            if el.g.consts.contains_key(&c) {
                continue
            }
            match all.get(&n) {
                Some(Declar::Recursor(sr)) if sr.all_inductives == rd.all_inductives && sr.info.uparams == rd.info.uparams => {
                    let Some(si) = rec_index(&block, &c) else { return Err(format!("{c} is not a recursor of the block")) };
                    el.g.consts.insert(c, ConstInfo { term: block.data, kind: ConstKind::Rec { i: si, large }, nlevels: nl, ty_thm: ThId(0) });
                }
                _ => return Err(format!("unknown constant {c}")),
            }
        }
    }
    let rhss: Vec<E> = rd.rec_rules.iter().map(|r| el.tr(r.val)).collect::<R<_>>()?;
    // `elim_ok` over any context, once: the iota lemmas take it at their own context
    let elim = if !el.g.replay && !rd.rec_rules.is_empty() {
        let g = &mut *el.g;
        let (d, v) = match g.env.head(rt) {
            Some((_, &[d, _, v])) => (d, v),
            _ => return Err("not a recursor term".into()),
        };
        let g0 = g.env.var(0);
        let goal = g.env.app_n("elim_ok", &[g0, d, v]);
        pv.horn.facts.clear();
        let p = pv.prove(g, goal)?;
        let mut name = format!("{}{}_elim", mm0kit::lean::FACT_PREFIX, sig.cname);
        while g.env.has_thm(&name) {
            name.push('_');
        }
        let la = g.g_args(&sig.lvl_names);
        Some(mm(g.env.add_lemma(&name, la.into(), p, crate::gen::split_budget()))?)
    } else {
        None
    };
    for (rule, &rhs) in rd.rec_rules.iter().zip(&rhss) {
        let ctor_lean = el.g.lean_name(el.tc, rule.ctor_name);
        let nf = rule.ctor_telescope_size_wo_params as usize;
        let g = &mut *el.g;
        let short = ctor_lean.rsplit('.').next().unwrap_or(&ctor_lean);
        let mut shift = vec![g.env.var(0)];
        shift.extend((0..nl).map(|i| g.env.var(i as u16)));
        let rhs0 = g.env.subst(rhs, &shift);
        let def_name = g.terms.fresh(&format!("{}_{}", sig.cname, mangle(short)));
        let expr_s = g.env.sort_names["expr"];
        let lvl_args = g.lvl_args(&sig.lvl_names);
        let def = add_term(&mut g.env, &def_name, lvl_args, expr_s, TermKind::Def { body: rhs0, public_body: true },
            &format!("The right-hand side of the iota rule of `{}` for `{ctor_lean}`.", sig.lean_name))?;
        // theorem R_closed (k) (us): closed k (R us): the closed equation is instantiated
        // through the definition
        g.lean.reset();
        let kv = g.env.var(0);
        let du = g.env.app(def, &us);
        let cl_concl = g.env.app_n("closed", &[kv, du]);
        let pc = if g.replay {
            None
        } else {
            let pc = mm(g.lean.closed(&mut g.env, kv, rhs))?;
            Some(mm(g.env.convert(pc, cl_concl))?)
        };
        let cl_args = g.k_args(&sig.lvl_names);
        let cl_name = g.thms.fresh(&format!("{def_name}_closed"));
        let cl = add_thm(&mut g.env, &cl_name, cl_args, vec![], cl_concl, false, false, pc, &format!("`{def_name}` has no loose bound variables."))?;
        g.lean.const_closed.insert(def, cl);
        let fixed = (rd.num_params + rd.num_motives + rd.num_minors) as usize;
        let name = g.thms.fresh(&format!("{def_name}_iota"));
        // an auxiliary type's constructor has the number of the nested block's
        let Some(&ConstInfo { kind: ConstKind::Ctor { c, .. }, .. }) = g.consts.get(&ctor_lean) else { return Err(format!("{ctor_lean} is not a constructor")) };
        let c = g.lean.nat(&mut g.env, c);
        let la = g.g_args(&sig.lvl_names);
        // the rule's premises `iota_eq` and `rst` make the schema's right-hand side the export's
        let th = iota_eq_lemma(g, &mut pv, la, &name, rt, c, du, fixed, nf, (wf, &us[nl - block.nlevels..]), elim,
            &format!("Iota reduction of `{}` on `{ctor_lean}`, as a closed equation.", sig.lean_name))
            .map_err(|e| format!("iota of `{}` on `{ctor_lean}` (the rule may not be the schema's): {e}", sig.lean_name))?;
        g.iota_eq.insert((sig.lean_name.clone(), ctor_lean), th);
    }
    Ok(true)
}
