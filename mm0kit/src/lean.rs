//! Proof producers for `spec/lean.mm0`: the side relations (`le`, `lt`, `add`, `closed`,
//! `lift`, `inst`, `lookup`) are proved syntax-directed, and the judgment rules are applied
//! with their arguments read off the premises.

use crate::bail;
use crate::env::*;
use rustc_hash::FxHashMap as HashMap;

/// Arithmetic facts about numerals (`le`, `add`) whose proofs take at least this many steps are
/// proved once, as lemmas without arguments, and cited: deep contexts make de Bruijn indices
/// large, and the chains would otherwise be re-proved in every theorem.
const FACT_STEPS: usize = 3;

/// The prefix of the names of lemmas made while proving (these facts, `Env::add_thm_split`'s
/// lemmas and the elaborator's closed lemmas). Generated names avoid it (see `nanoda`'s
/// `Names`), so the names of public statements do not depend on which lemmas were made, and
/// sharded generation (`mmb::merge`) can tell lemmas from the rest by name.
pub const FACT_PREFIX: &str = "lean0_";

/// The term constructors of `lean.mm0` that the provers inspect.
#[derive(Clone, Copy)]
pub struct Ids {
    pub z: TId,
    pub s: TId,
    pub bvar: TId,
    pub srt: TId,
    pub app: TId,
    pub lam: TId,
    pub pi: TId,
    pub nil: TId,
    pub cons: TId,
    pub lz: TId,
    pub ls: TId,
    pub lmax: TId,
    pub limax: TId,
    pub deq: TId,
    pub ty: TId,
    pub lt: TId,
    pub closed: TId,
}

/// An `expr`-level view of an MM0 expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum View {
    BVar(usize),
    Srt(E),
    App(E, E),
    Lam(E, E),
    Pi(E, E),
    /// A constant (a generated `term` or `def` whose arguments are all levels), or a Nat
    /// literal `lit n`.
    Const(TId),
    /// A projection `S_proj i e` of a structure `S` (a generated term).
    Proj(E, usize, E),
    /// Anything else (a variable of sort `expr`, which generated proofs never contain).
    Other,
}

#[derive(Clone, Copy, Debug)]
pub struct ProjRules {
    pub closed: ThId,
    pub lift: ThId,
    pub inst: ThId,
}

pub struct Lean {
    pub ids: Ids,
    /// The spec's `proj` term (`proj b i e`), if the spec has it.
    pub proj_id: Option<TId>,
    nats: Vec<E>,
    /// The spec's numerals `n1`..`n9` (definitions of `s^k nz`), by their term.
    numerals: HashMap<TId, usize>,
    /// `closed k (c us)` lemma for each constant (by its head term), taking `k` then the levels.
    pub const_closed: HashMap<TId, ThId>,
    /// The structural `closed`, `lift` and `inst` axioms of `proj`.
    pub proj_rules: Option<ProjRules>,
    fvb_memo: HashMap<E, usize>,
    memo_closed: HashMap<(usize, E), P>,
    memo_lift: HashMap<(usize, usize, E), (E, P)>,
    memo_inst: HashMap<(usize, E, E), (E, P)>,
    memo_lookup: HashMap<(E, usize), (E, P)>,
    /// `inst_pure` and `lift_pure`: terms are DAGs (nested `let`s inline into them), so an
    /// unmemoized traversal can take exponential time.
    memo_inst_pure: HashMap<(usize, E, E), E>,
    memo_lift_pure: HashMap<(usize, usize, E), E>,
}

impl Lean {
    /// The spec's numerals and `Prop` become abbreviations (`Env::set_abbreviations`): proofs
    /// only see `s` chains and `srt lz`, as `nat` and the elaborator build them.
    pub fn new(env: &mut Env) -> Self {
        let t = |n: &str| env.term_id(n);
        let ids = Ids {
            z: t("nz"),
            s: t("s"),
            bvar: t("bvar"),
            srt: t("srt"),
            app: t("app"),
            lam: t("lam"),
            pi: t("pi"),
            nil: t("nil"),
            cons: t("cons"),
            lz: t("lz"),
            ls: t("ls"),
            lmax: t("lmax"),
            limax: t("limax"),
            deq: t("deq"),
            ty: t("ty"),
            lt: t("lt"),
            closed: t("closed"),
        };
        let mut const_closed = HashMap::default();
        // a Nat literal `lit n` is closed like a constant, and so are the inductive constants
        for (term, ax) in [("lit", "closed_lit"), ("cst", "closed_cst"), ("ind_ty", "closed_ind_ty"), ("ind_ctor", "closed_ind_ctor"), ("ind_rec", "closed_ind_rec"),
            ("quot", "closed_quot"), ("quot_mk", "closed_quot_mk"), ("quot_lift", "closed_quot_lift"), ("quot_ind", "closed_quot_ind")] {
            if env.has_term(term) && env.has_thm(ax) {
                const_closed.insert(t(term), env.thm_id(ax));
            }
        }
        let numerals: HashMap<TId, usize> =
            (1..=9).map(|k| (format!("n{k}"), k)).filter(|(n, _)| env.has_term(n)).map(|(n, k)| (t(&n), k)).collect();
        let proj_id = env.has_term("proj").then(|| t("proj"));
        let proj_rules = proj_id.filter(|_| env.has_thm("closed_proj")).map(|_| ProjRules {
            closed: env.thm_id("closed_proj"),
            lift: env.thm_id("lift_proj"),
            inst: env.thm_id("inst_proj"),
        });
        let mut abbreviations: Vec<TId> = numerals.keys().copied().collect();
        abbreviations.extend(env.has_term("Prop").then(|| t("Prop")));
        env.set_abbreviations(&abbreviations);
        Lean {
            ids,
            proj_id,
            nats: Vec::new(),
            numerals,
            const_closed,
            proj_rules,
            fvb_memo: HashMap::default(),
            memo_closed: HashMap::default(),
            memo_lift: HashMap::default(),
            memo_inst: HashMap::default(),
            memo_inst_pure: HashMap::default(),
            memo_lift_pure: HashMap::default(),
            memo_lookup: HashMap::default(),
        }
    }

    /// Forget memoized proofs. Proofs mention statement variables, so they are only reused
    /// within one statement.
    pub fn reset(&mut self) {
        clear_and_shrink(&mut self.memo_closed);
        clear_and_shrink(&mut self.memo_lift);
        clear_and_shrink(&mut self.memo_inst);
        clear_and_shrink(&mut self.memo_lookup);
        clear_and_shrink(&mut self.memo_inst_pure);
        clear_and_shrink(&mut self.memo_lift_pure);
    }

    /// After `Env::compact_nodes(n, ..)` with the renaming `map`: follow it, and forget what
    /// mentions dropped nodes. `nats` must have been among the roots.
    pub fn remap_nodes(&mut self, n: usize, map: &HashMap<E, E>) {
        self.reset();
        for e in &mut self.nats {
            if e.0 as usize >= n {
                *e = map[e];
            }
        }
        self.fvb_memo.retain(|e, _| (e.0 as usize) < n);
    }

    /// The unary numerals made so far (roots for `Env::compact_nodes`).
    pub fn nats(&self) -> &[E] { &self.nats }

    // ------------------------------------------------------------------ syntax

    pub fn nat(&mut self, env: &mut Env, n: usize) -> E {
        while self.nats.len() <= n {
            let e = match self.nats.last() {
                None => env.app(self.ids.z, &[]),
                Some(&p) => env.app(self.ids.s, &[p]),
            };
            self.nats.push(e);
        }
        self.nats[n]
    }

    pub fn nat_val(&self, env: &Env, mut e: E) -> Option<usize> {
        let mut n = 0;
        loop {
            match env.head(e)? {
                (t, []) if t == self.ids.z => return Some(n),
                (t, [p]) if t == self.ids.s => {
                    n += 1;
                    e = *p
                }
                (t, []) => return Some(n + self.numerals.get(&t)?),
                _ => return None,
            }
        }
    }

    pub fn view(&self, env: &Env, e: E) -> View {
        let Some((t, args)) = env.head(e) else { return View::Other };
        let i = &self.ids;
        match args {
            [n] if t == i.bvar => View::BVar(self.nat_val(env, *n).expect("bvar index")),
            [l] if t == i.srt => View::Srt(*l),
            [f, a] if t == i.app => View::App(*f, *a),
            [a, b] if t == i.lam => View::Lam(*a, *b),
            [a, b] if t == i.pi => View::Pi(*a, *b),
            [b, n, e] if Some(t) == self.proj_id => View::Proj(*b, self.nat_val(env, *n).expect("projection index"), *e),
            _ if env.terms[t.0 as usize].ret == env.terms[i.bvar.0 as usize].ret => View::Const(t),
            _ => View::Other,
        }
    }

    pub fn bvar(&mut self, env: &mut Env, i: usize) -> E {
        let n = self.nat(env, i);
        env.app(self.ids.bvar, &[n])
    }
    pub fn srt(&self, env: &mut Env, l: E) -> E { env.app(self.ids.srt, &[l]) }
    pub fn app(&self, env: &mut Env, f: E, a: E) -> E { env.app(self.ids.app, &[f, a]) }
    pub fn lam(&self, env: &mut Env, a: E, b: E) -> E { env.app(self.ids.lam, &[a, b]) }
    pub fn pi(&self, env: &mut Env, a: E, b: E) -> E { env.app(self.ids.pi, &[a, b]) }
    /// `proj b i e`, for the block atom `b`.
    pub fn proj(&mut self, env: &mut Env, b: E, i: usize, e: E) -> E {
        let ie = self.nat(env, i);
        let t = self.proj_id.expect("the spec has no proj term");
        env.app(t, &[b, ie, e])
    }
    pub fn cons(&self, env: &mut Env, a: E, g: E) -> E { env.app(self.ids.cons, &[a, g]) }
    pub fn deq(&self, env: &mut Env, g: E, a: E, b: E, t: E) -> E { env.app(self.ids.deq, &[g, a, b, t]) }

    /// `(G, e, e2, A)` of a `deq G e e2 A` (also accepting `ty G e A`).
    pub fn deq_parts(&self, env: &mut Env, p: P) -> (E, E, E, E) {
        let e = env.concl(p);
        match env.head(e) {
            Some((t, [g, a, b, ty])) if t == self.ids.deq => (*g, *a, *b, *ty),
            Some((t, [g, a, ty])) if t == self.ids.ty => (*g, *a, *a, *ty),
            _ => panic!("not a deq: {}", env.show(e, &[])),
        }
    }

    /// One plus the largest loose de Bruijn index of `e` (0 if it has none).
    pub fn fvb(&mut self, env: &Env, e: E) -> usize {
        if let Some(&r) = self.fvb_memo.get(&e) {
            return r
        }
        let r = match self.view(env, e) {
            View::BVar(i) => i + 1,
            View::Srt(_) | View::Const(_) | View::Other => 0,
            View::App(f, a) => self.fvb(env, f).max(self.fvb(env, a)),
            View::Lam(a, b) | View::Pi(a, b) => self.fvb(env, a).max(self.fvb(env, b).saturating_sub(1)),
            View::Proj(_, _, x) => self.fvb(env, x),
        };
        self.fvb_memo.insert(e, r);
        r
    }

    /// `liftN n e k` as an expression, without a proof.
    pub fn lift_pure(&mut self, env: &mut Env, n: usize, k: usize, e: E) -> E {
        if self.fvb(env, e) <= k {
            return e
        }
        if let Some(&r) = self.memo_lift_pure.get(&(n, k, e)) {
            return r
        }
        let r = match self.view(env, e) {
            View::BVar(i) if i < k => e,
            View::BVar(i) => self.bvar(env, i + n),
            View::App(f, a) => {
                let (f, a) = (self.lift_pure(env, n, k, f), self.lift_pure(env, n, k, a));
                self.app(env, f, a)
            }
            View::Lam(a, b) => {
                let (a, b) = (self.lift_pure(env, n, k, a), self.lift_pure(env, n, k + 1, b));
                self.lam(env, a, b)
            }
            View::Pi(a, b) => {
                let (a, b) = (self.lift_pure(env, n, k, a), self.lift_pure(env, n, k + 1, b));
                self.pi(env, a, b)
            }
            View::Proj(b, i, x) => {
                let x = self.lift_pure(env, n, k, x);
                self.proj(env, b, i, x)
            }
            _ => e,
        };
        self.memo_lift_pure.insert((n, k, e), r);
        r
    }

    /// `inst e a k` as an expression, without a proof.
    pub fn inst_pure(&mut self, env: &mut Env, k: usize, e: E, a: E) -> E {
        if self.fvb(env, e) <= k {
            return e
        }
        if let Some(&r) = self.memo_inst_pure.get(&(k, e, a)) {
            return r
        }
        let r = match self.view(env, e) {
            View::BVar(i) if i < k => e,
            View::BVar(i) if i == k => self.lift_pure(env, k, 0, a),
            View::BVar(i) => self.bvar(env, i - 1),
            View::App(f, x) => {
                let (f, x) = (self.inst_pure(env, k, f, a), self.inst_pure(env, k, x, a));
                self.app(env, f, x)
            }
            View::Lam(t, b) => {
                let (t, b) = (self.inst_pure(env, k, t, a), self.inst_pure(env, k + 1, b, a));
                self.lam(env, t, b)
            }
            View::Pi(t, b) => {
                let (t, b) = (self.inst_pure(env, k, t, a), self.inst_pure(env, k + 1, b, a));
                self.pi(env, t, b)
            }
            View::Proj(b, i, x) => {
                let x = self.inst_pure(env, k, x, a);
                self.proj(env, b, i, x)
            }
            _ => e,
        };
        self.memo_inst_pure.insert((k, e, a), r);
        r
    }

    // ------------------------------------------------------------------ naturals

    /// `le i n`, for literal naturals.
    pub fn le(&mut self, env: &mut Env, i: usize, n: usize) -> Result<P> {
        if i > n {
            bail!("le {i} {n} is false")
        }
        let mut p = {
            let m = self.nat(env, n - i);
            env.thm_n("le_z", &[m], &[])?
        };
        for d in 1..=i {
            let (a, b) = (self.nat(env, d - 1), self.nat(env, n - i + d - 1));
            p = env.thm_n("le_s", &[a, b], &[p])?;
        }
        fact(env, &format!("{FACT_PREFIX}le_{i}_{n}"), p, i + 1)
    }

    /// `le i k` where `k` is an arbitrary nat expression `s^m k0`: needs `i <= m`.
    pub fn le_e(&mut self, env: &mut Env, i: usize, k: E) -> Result<P> {
        if let Some(m) = self.nat_val(env, k) {
            return self.le(env, i, m)
        }
        // peel `i` successors off `k`
        let mut ks = vec![k];
        for _ in 0..i {
            let cur = *ks.last().unwrap();
            match env.head(cur) {
                Some((t, [p])) if t == self.ids.s => ks.push(*p),
                _ => bail!("le {i} {}: not enough successors", env.show(k, &[])),
            }
        }
        let mut p = env.thm_n("le_z", &[*ks.last().unwrap()], &[])?;
        for d in 1..=i {
            let a = self.nat(env, d - 1);
            p = env.thm_n("le_s", &[a, ks[i - d + 1]], &[p])?;
        }
        Ok(p)
    }

    /// `lt i k` (a def: `le (s i) k`).
    pub fn lt_e(&mut self, env: &mut Env, i: usize, k: E) -> Result<P> {
        let p = self.le_e(env, i + 1, k)?;
        let ie = self.nat(env, i);
        let target = env.app(self.ids.lt, &[ie, k]);
        env.convert(p, target)
    }

    /// `add i n (i + n)`.
    pub fn add(&mut self, env: &mut Env, i: usize, n: usize) -> Result<P> {
        let ie = self.nat(env, i);
        let mut p = env.thm_n("add_z", &[ie], &[])?;
        for d in 1..=n {
            let (a, b) = (self.nat(env, d - 1), self.nat(env, i + d - 1));
            p = env.thm_n("add_s", &[ie, a, b], &[p])?;
        }
        fact(env, &format!("{FACT_PREFIX}add_{i}_{n}"), p, n + 1)
    }

    // ------------------------------------------------------------------ closed / lift / inst

    /// `closed k e`, where `k` is a nat expression with at least `fvb(e)` successors.
    pub fn closed(&mut self, env: &mut Env, k: E, e: E) -> Result<P> {
        let key = (k.0 as usize, e);
        if let Some(&p) = self.memo_closed.get(&key) {
            return Ok(p)
        }
        let p = match self.view(env, e) {
            View::BVar(i) => {
                let lt = self.lt_e(env, i, k)?;
                let ie = self.nat(env, i);
                env.thm_n("closed_bvar", &[ie, k], &[lt])?
            }
            View::Srt(l) => env.thm_n("closed_srt", &[k, l], &[])?,
            View::App(f, a) => {
                let (pf, pa) = (self.closed(env, k, f)?, self.closed(env, k, a)?);
                env.thm_n("closed_app", &[k, f, a], &[pf, pa])?
            }
            View::Lam(a, b) | View::Pi(a, b) => {
                let sk = env.app(self.ids.s, &[k]);
                let (pa, pb) = (self.closed(env, k, a)?, self.closed(env, sk, b)?);
                let r = if matches!(self.view(env, e), View::Lam(..)) { "closed_lam" } else { "closed_pi" };
                env.thm_n(r, &[k, a, b], &[pa, pb])?
            }
            View::Proj(b, i, x) => {
                let px = self.closed(env, k, x)?;
                let (th, ie) = (self.proj_rules.as_ref().unwrap().closed, self.nat(env, i));
                env.thm(th, &[k, b, ie, x], &[px])?
            }
            View::Const(t) => {
                let Some(&th) = self.const_closed.get(&t) else { bail!("no closedness lemma for {}", env.terms[t.0 as usize].name) };
                let mut args = vec![k];
                args.extend_from_slice(env.head(e).unwrap().1);
                env.thm(th, &args, &[])?
            }
            View::Other => bail!("closed: unexpected expression {}", env.show(e, &[])),
        };
        self.memo_closed.insert(key, p);
        Ok(p)
    }

    /// `lift n k e e2`: returns `e2` and the proof.
    pub fn lift(&mut self, env: &mut Env, n: usize, k: usize, e: E) -> Result<(E, P)> {
        if let Some(&r) = self.memo_lift.get(&(n, k, e)) {
            return Ok(r)
        }
        let (ne, ke) = (self.nat(env, n), self.nat(env, k));
        let j = self.fvb(env, e);
        let r = if j <= k && !matches!(self.view(env, e), View::BVar(_) | View::Srt(_)) {
            let je = self.nat(env, j);
            let pc = self.closed(env, je, e)?;
            let pl = self.le(env, j, k)?;
            (e, env.thm_n("lift_closed", &[ne, je, ke, e], &[pc, pl])?)
        } else {
            match self.view(env, e) {
                View::BVar(i) if i < k => {
                    let lt = self.lt_e(env, i, ke)?;
                    let ie = self.nat(env, i);
                    (e, env.thm_n("lift_bvar_lt", &[ne, ke, ie], &[lt])?)
                }
                View::BVar(i) => {
                    let le = self.le(env, k, i)?;
                    let add = self.add(env, i, n)?;
                    let (ie, je) = (self.nat(env, i), self.nat(env, i + n));
                    let e2 = env.app(self.ids.bvar, &[je]);
                    (e2, env.thm_n("lift_bvar_ge", &[ne, ke, ie, je], &[le, add])?)
                }
                View::Srt(l) => (e, env.thm_n("lift_srt", &[ne, ke, l], &[])?),
                View::App(f, a) => {
                    let ((f2, pf), (a2, pa)) = (self.lift(env, n, k, f)?, self.lift(env, n, k, a)?);
                    (self.app(env, f2, a2), env.thm_n("lift_app", &[ne, ke, f, a, f2, a2], &[pf, pa])?)
                }
                v @ (View::Lam(a, b) | View::Pi(a, b)) => {
                    let ((a2, pa), (b2, pb)) = (self.lift(env, n, k, a)?, self.lift(env, n, k + 1, b)?);
                    let (e2, r) = if matches!(v, View::Lam(..)) {
                        (self.lam(env, a2, b2), "lift_lam")
                    } else {
                        (self.pi(env, a2, b2), "lift_pi")
                    };
                    (e2, env.thm_n(r, &[ne, ke, a, b, a2, b2], &[pa, pb])?)
                }
                View::Proj(b, i, x) => {
                    let (x2, px) = self.lift(env, n, k, x)?;
                    let (th, ie) = (self.proj_rules.as_ref().unwrap().lift, self.nat(env, i));
                    (self.proj(env, b, i, x2), env.thm(th, &[ne, ke, b, ie, x, x2], &[px])?)
                }
                _ => bail!("lift: unexpected expression {}", env.show(e, &[])),
            }
        };
        self.memo_lift.insert((n, k, e), r);
        Ok(r)
    }

    /// `inst k e a e2`: returns `e2` and the proof.
    pub fn inst(&mut self, env: &mut Env, k: usize, e: E, a: E) -> Result<(E, P)> {
        if let Some(&r) = self.memo_inst.get(&(k, e, a)) {
            return Ok(r)
        }
        let ke = self.nat(env, k);
        let j = self.fvb(env, e);
        let r = if j <= k && !matches!(self.view(env, e), View::BVar(_) | View::Srt(_)) {
            let je = self.nat(env, j);
            let pc = self.closed(env, je, e)?;
            let pl = self.le(env, j, k)?;
            (e, env.thm_n("inst_closed", &[je, ke, e, a], &[pc, pl])?)
        } else {
            match self.view(env, e) {
                View::BVar(i) if i < k => {
                    let lt = self.lt_e(env, i, ke)?;
                    let ie = self.nat(env, i);
                    (e, env.thm_n("inst_bvar_lt", &[ke, ie, a], &[lt])?)
                }
                View::BVar(i) if i == k => {
                    let (a2, pl) = self.lift(env, k, 0, a)?;
                    (a2, env.thm_n("inst_bvar_eq", &[ke, a, a2], &[pl])?)
                }
                View::BVar(i) => {
                    let le = self.le(env, k, i - 1)?;
                    let ie = self.nat(env, i - 1);
                    let e2 = env.app(self.ids.bvar, &[ie]);
                    (e2, env.thm_n("inst_bvar_gt", &[ke, ie, a], &[le])?)
                }
                View::Srt(l) => (e, env.thm_n("inst_srt", &[ke, l, a], &[])?),
                View::App(f, x) => {
                    let ((f2, pf), (x2, px)) = (self.inst(env, k, f, a)?, self.inst(env, k, x, a)?);
                    (self.app(env, f2, x2), env.thm_n("inst_app", &[ke, f, x, a, f2, x2], &[pf, px])?)
                }
                v @ (View::Lam(ty, b) | View::Pi(ty, b)) => {
                    let ((t2, pt), (b2, pb)) = (self.inst(env, k, ty, a)?, self.inst(env, k + 1, b, a)?);
                    let (e2, r) = if matches!(v, View::Lam(..)) {
                        (self.lam(env, t2, b2), "inst_lam")
                    } else {
                        (self.pi(env, t2, b2), "inst_pi")
                    };
                    (e2, env.thm_n(r, &[ke, ty, b, a, t2, b2], &[pt, pb])?)
                }
                View::Proj(b, i, x) => {
                    let (x2, px) = self.inst(env, k, x, a)?;
                    let (th, ie) = (self.proj_rules.as_ref().unwrap().inst, self.nat(env, i));
                    (self.proj(env, b, i, x2), env.thm(th, &[ke, b, ie, x, a, x2], &[px])?)
                }
                _ => bail!("inst: unexpected expression {}", env.show(e, &[])),
            }
        };
        self.memo_inst.insert((k, e, a), r);
        Ok(r)
    }

    /// `lookup G i A`: returns `A` and the proof. `G` must be a `cons` chain of length > `i`.
    pub fn lookup(&mut self, env: &mut Env, g: E, i: usize) -> Result<(E, P)> {
        if let Some(&r) = self.memo_lookup.get(&(g, i)) {
            return Ok(r)
        }
        let Some((t, &[a, g2])) = env.head(g) else { bail!("lookup in a context variable") };
        if t != self.ids.cons {
            bail!("lookup: not a cons")
        }
        let r = if i == 0 {
            let (a2, pl) = self.lift(env, 1, 0, a)?;
            (a2, env.thm_n("lookup_z", &[a, a2, g2], &[pl])?)
        } else {
            let (b, pb) = self.lookup(env, g2, i - 1)?;
            let (b2, pl) = self.lift(env, 1, 0, b)?;
            let n = self.nat(env, i - 1);
            (b2, env.thm_n("lookup_s", &[a, b, b2, g2, n], &[pb, pl])?)
        };
        self.memo_lookup.insert((g, i), r);
        Ok(r)
    }

    // ------------------------------------------------------------------ judgment rules

    pub fn bvar_rule(&mut self, env: &mut Env, g: E, i: usize) -> Result<P> {
        let (a, pl) = self.lookup(env, g, i)?;
        let ie = self.nat(env, i);
        let p = env.thm_n("bvar", &[g, ie, a], &[pl])?;
        // the rule concludes `ty`; derivations are `deq`
        let e = self.bvar(env, i);
        let target = env.app(self.ids.deq, &[g, e, e, a]);
        env.convert(p, target)
    }

    pub fn symm(&mut self, env: &mut Env, p: P) -> Result<P> {
        let (g, a, b, t) = self.deq_parts(env, p);
        env.thm_n("symm", &[g, a, b, t], &[p])
    }

    pub fn trans(&mut self, env: &mut Env, p: P, q: P) -> Result<P> {
        let (g, a, b, t) = self.deq_parts(env, p);
        let (_, b2, c, _) = self.deq_parts(env, q);
        if b != b2 {
            bail!("trans: middle terms differ:\n  {}\n  {}", env.show(b, &[]), env.show(b2, &[]))
        }
        env.thm_n("trans", &[g, a, b, c, t], &[p, q])
    }

    /// `ty G e A` from `deq G e e2 A`.
    pub fn refl_l(&mut self, env: &mut Env, p: P) -> Result<P> {
        let q = self.symm(env, p)?;
        self.trans(env, p, q)
    }

    /// `ty G e2 A` from `deq G e e2 A`.
    pub fn refl_r(&mut self, env: &mut Env, p: P) -> Result<P> {
        let q = self.symm(env, p)?;
        self.trans(env, q, p)
    }

    /// `sortDF` from a `leqv l l2` proof.
    pub fn sort_df(&mut self, env: &mut Env, g: E, l: E, l2: E, pl: P) -> Result<P> {
        env.thm_n("sortDF", &[g, l, l2], &[pl])
    }

    /// `appDF`: `pf: deq G f f2 (pi A B)`, `pa: deq G a a2 A`.
    pub fn app_df(&mut self, env: &mut Env, pf: P, pa: P) -> Result<P> {
        let (g, f, f2, fty) = self.deq_parts(env, pf);
        let View::Pi(a, b) = self.view(env, fty) else { bail!("appDF: function type is not a pi: {}", env.show(fty, &[])) };
        let (_, x, x2, _) = self.deq_parts(env, pa);
        let (r, pi) = self.inst(env, 0, b, x)?;
        env.thm_n("appDF", &[g, f, f2, a, b, x, x2, r], &[pf, pa, pi])
    }

    /// `sty_nil`: `sty G h A h A`.
    pub fn sty_nil(&mut self, env: &mut Env, g: E, h: E, a: E) -> Result<P> {
        env.thm_n("sty_nil", &[g, h, a], &[])
    }

    /// `sty_app`: `ps: sty G h A f (pi B C)`, `pa: ty G a B`; the conclusion is
    /// `sty G h A (app f a) C2` with `C2` the instantiation of `C` at `a`.
    pub fn sty_app(&mut self, env: &mut Env, ps: P, pa: P) -> Result<P> {
        let c = env.concl(ps);
        let sty = env.term_id("sty");
        let Some((t, &[g, h, a0, f, fty])) = env.head(c) else { bail!("sty_app: not an sty: {}", env.show(c, &[])) };
        if t != sty {
            bail!("sty_app: not an sty: {}", env.show(c, &[]))
        }
        let View::Pi(b, cb) = self.view(env, fty) else { bail!("sty_app: the head's type is not a pi here: {}", env.show(fty, &[])) };
        let (_, x, _, xty) = self.deq_parts(env, pa);
        if xty != b {
            bail!("sty_app: argument type mismatch:\n  {}\n  {}", env.show(xty, &[]), env.show(b, &[]))
        }
        let (c2, pi) = self.inst(env, 0, cb, x)?;
        env.thm_n("sty_app", &[g, h, a0, f, x, b, cb, c2], &[ps, pa, pi])
    }

    /// `lamDF`: `pa: deq G A A2 (srt u)`, `pb: deq (cons A G) b b2 B`.
    pub fn lam_df(&mut self, env: &mut Env, pa: P, pb: P) -> Result<P> {
        let (g, a, a2, aty) = self.deq_parts(env, pa);
        let View::Srt(u) = self.view(env, aty) else { bail!("lamDF: domain type is not a sort") };
        let (_, b, b2, bty) = self.deq_parts(env, pb);
        env.thm_n("lamDF", &[g, u, a, a2, b, b2, bty], &[pa, pb])
    }

    /// `forallEDF`: `pa: deq G A A2 (srt u)`, `pb: deq (cons A G) B B2 (srt v)`.
    pub fn forall_df(&mut self, env: &mut Env, pa: P, pb: P) -> Result<P> {
        let (g, a, a2, aty) = self.deq_parts(env, pa);
        let View::Srt(u) = self.view(env, aty) else { bail!("forallEDF: domain type is not a sort") };
        let (_, b, b2, bty) = self.deq_parts(env, pb);
        let View::Srt(v) = self.view(env, bty) else { bail!("forallEDF: body type is not a sort") };
        env.thm_n("forallEDF", &[g, u, v, a, a2, b, b2], &[pa, pb])
    }

    /// `defeqDF`: `pt: deq G A B (srt u)`, `pe: deq G e e2 A`.
    pub fn defeq_df(&mut self, env: &mut Env, pt: P, pe: P) -> Result<P> {
        let (g, a, b, tty) = self.deq_parts(env, pt);
        let View::Srt(u) = self.view(env, tty) else { bail!("defeqDF: type equation is not at a sort") };
        let (_, e, e2, ety) = self.deq_parts(env, pe);
        if ety != a {
            bail!("defeqDF: type mismatch:\n  {}\n  {}", env.show(ety, &[]), env.show(a, &[]))
        }
        env.thm_n("defeqDF", &[g, u, a, b, e, e2], &[pt, pe])
    }

    /// `beta`: `pb: ty (cons A G) e B`, `pa: ty G a A`.
    pub fn beta(&mut self, env: &mut Env, pb: P, pa: P) -> Result<P> {
        let (ga, e, _, bty) = self.deq_parts(env, pb);
        let (g, a, _, aty) = self.deq_parts(env, pa);
        let Some((t, &[cty, _])) = env.head(ga) else { bail!("beta: body context") };
        debug_assert_eq!(t, self.ids.cons);
        if cty != aty {
            bail!("beta: argument type mismatch")
        }
        let (r, pr) = self.inst(env, 0, e, a)?;
        let (rt, prt) = self.inst(env, 0, bty, a)?;
        env.thm_n("beta", &[g, aty, e, bty, a, r, rt], &[pb, pa, pr, prt])
    }

    /// `cinst k G0 A0 a G1 G` for the context `G1`: returns `(G0, A0, G)` and the proof.
    pub fn cinst(&mut self, env: &mut Env, k: usize, g1: E, a: E) -> Result<(E, E, E, P)> {
        let Some((t, &[b, g1t])) = env.head(g1) else { bail!("cinst: context too short") };
        if t != self.ids.cons {
            bail!("cinst: not a cons")
        }
        if k == 0 {
            return Ok((g1t, b, g1t, env.thm_n("cinst_z", &[g1t, b, a], &[])?))
        }
        let (g0, a0, g, p) = self.cinst(env, k - 1, g1t, a)?;
        let (b2, pb) = self.inst(env, k - 1, b, a)?;
        let ke = self.nat(env, k - 1);
        let p = env.thm_n("cinst_s", &[ke, g0, g1t, g, a0, a, b, b2], &[p, pb])?;
        Ok((g0, a0, self.cons(env, b2, g), p))
    }

    /// `instDF`: `pa: ty G0 a A0` and `p: deq G1 e e2 A`, where `G1` has `A0` over `G0` and then
    /// `k` more entries, give `deq G e[a] e2[a] A[a]` (substituting at `k`).
    pub fn inst_df(&mut self, env: &mut Env, k: usize, pa: P, p: P) -> Result<P> {
        let (g0a, a, _, a0a) = self.deq_parts(env, pa);
        let (g1, e, e2, ty) = self.deq_parts(env, p);
        let (g0, a0, g, pc) = self.cinst(env, k, g1, a)?;
        if g0 != g0a {
            bail!("instDF: the argument's context does not match the substituted entry's")
        }
        // the entry may be the argument's type up to definitions (a type that went through
        // the schema's relations has its definitions unfolded)
        let pa = if a0 == a0a {
            pa
        } else {
            let c = env.concl(pa);
            let (t, xs) = env.head(c).unwrap();
            let mut xs = xs.to_vec();
            *xs.last_mut().unwrap() = a0;
            let target = env.app(t, &xs);
            env.convert(pa, target).map_err(|_| Mm0Error("instDF: the argument's type does not match the substituted entry".into()))?
        };
        let ((r, pr), (r2, pr2), (rt, prt)) = (self.inst(env, k, e, a)?, self.inst(env, k, e2, a)?, self.inst(env, k, ty, a)?);
        let ke = self.nat(env, k);
        env.thm_n("instDF", &[ke, g0, g1, g, a0, a, e, e2, ty, r, r2, rt], &[pa, pc, p, pr, pr2, prt])
    }

    /// `cext n G G2` for the context `G2`: returns `G` and the proof.
    pub fn cext(&mut self, env: &mut Env, n: usize, g2: E) -> Result<(E, P)> {
        if n == 0 {
            return Ok((g2, env.thm_n("cext_z", &[g2], &[])?))
        }
        let Some((t, &[a, g2t])) = env.head(g2) else { bail!("cext: context too short") };
        if t != self.ids.cons {
            bail!("cext: not a cons")
        }
        let (g, p) = self.cext(env, n - 1, g2t)?;
        let ne = self.nat(env, n - 1);
        Ok((g, env.thm_n("cext_s", &[ne, g, g2t, a], &[p])?))
    }

    /// `weakDF`: `p: deq G e e2 A`, where `G` is `G2` without its last `n` entries, gives
    /// `deq G2 e↑ e2↑ A↑` (lifting by `n`).
    pub fn weak_df(&mut self, env: &mut Env, n: usize, g2: E, p: P) -> Result<P> {
        let (g, e, e2, ty) = self.deq_parts(env, p);
        let (g0, pc) = self.cext(env, n, g2)?;
        if g0 != g {
            bail!("weakDF: the context is not a prefix")
        }
        let ((r, pr), (r2, pr2), (rt, prt)) = (self.lift(env, n, 0, e)?, self.lift(env, n, 0, e2)?, self.lift(env, n, 0, ty)?);
        let ne = self.nat(env, n);
        env.thm_n("weakDF", &[ne, g, g2, e, e2, ty, r, r2, rt], &[p, pc, pr, pr2, prt])
    }

    /// `eta`: `pe: ty G e (pi A B)` gives `deq G (lam A (app e↑ #0)) e (pi A B)`.
    pub fn eta(&mut self, env: &mut Env, pe: P) -> Result<P> {
        let (g, e, _, ety) = self.deq_parts(env, pe);
        let View::Pi(a, b) = self.view(env, ety) else { bail!("eta: not a pi type") };
        let (e1, pl) = self.lift(env, 1, 0, e)?;
        env.thm_n("eta", &[g, a, b, e, e1], &[pe, pl])
    }

    /// `proofIrrel`: `pp: ty G p (srt lz)`, `ph: ty G h p`, `ph2: ty G h2 p`.
    pub fn proof_irrel(&mut self, env: &mut Env, pp: P, ph: P, ph2: P) -> Result<P> {
        let (g, p, _, _) = self.deq_parts(env, pp);
        let (_, h, _, _) = self.deq_parts(env, ph);
        let (_, h2, _, _) = self.deq_parts(env, ph2);
        env.thm_n("proofIrrel", &[g, p, h, h2], &[pp, ph, ph2])
    }
}

/// Clear a memo table, giving its memory back if it grew large (`clear` keeps the capacity,
/// which a large declaration leaves large).
fn clear_and_shrink<K: Eq + std::hash::Hash, V>(m: &mut HashMap<K, V>) {
    let big = m.capacity() > 1 << 16;
    m.clear();
    if big {
        m.shrink_to_fit();
    }
}

/// A variable-free fact proved by `p` in `steps` steps: if it is long enough, a citation of the
/// shared lemma `name` for it (made now if there is none yet).
fn fact(env: &mut Env, name: &str, p: P, steps: usize) -> Result<P> {
    if steps < FACT_STEPS {
        return Ok(p)
    }
    let id = env.add_lemma(name, Args::from(Vec::new()), p, usize::MAX)?;
    env.thm(id, &[], &[])
}
