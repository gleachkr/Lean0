//! A generic prover for the spec's syntax-directed relations, read as Horn clauses.
//!
//! A goal is a `wff` term that may contain metavariables (outputs). It is proved by
//! depth-first search over the clauses whose conclusion has the goal's head: the clause's
//! variables become fresh metavariables, its conclusion is unified with the goal, and its
//! premises are proved left to right; on failure the bindings are undone and the next
//! clause is tried. A relation whose clauses are exclusive by the shape of their inputs
//! (as every relation of the inductive schema is, audit §4) needs no backtracking, so
//! this is linear in the size of the derivation.
//!
//! Some heads are not searched: `deq` and `ty` go to the caller's [`Hooks`] (typing
//! facts it already has), `leqv` to the level engine, and `lift`, `inst` and `closed`
//! with literal indices to the memoized provers in [`Lean`]. Unification unfolds a public
//! definition when its head meets a different head, so a block named by a definition
//! (`List_D u`) matches the clause pattern `ind_mk b P T`; the proof's conclusion is then
//! converted back to the goal as stated.
use crate::env::*;
use crate::bail;
use crate::lean::Lean;
use crate::level::Levels;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};


/// Proves goals the clauses do not cover (typing).
pub trait Hooks {
    /// Prove `goal`, binding its metavariables through [`Horn::unify`], or `None` to leave
    /// it to the clauses. `Some(Err(_))` fails the goal.
    fn prove(&mut self, h: &mut Horn, env: &mut Env, lean: &mut Lean, lv: &mut Levels, goal: E) -> Option<Result<P>>;
}

/// No hooks: typing goals fail.
pub struct NoHooks;
impl Hooks for NoHooks {
    fn prove(&mut self, _: &mut Horn, _: &mut Env, _: &mut Lean, _: &mut Levels, _: E) -> Option<Result<P>> { None }
}

#[derive(Clone)]
struct Ids {
    lift: TId,
    inst: TId,
    closed: TId,
    leqv: TId,
    deq: TId,
    add: TId,
    le: TId,
    ls: TId,
    lmax: TId,
    limax: TId,
}

/// The clauses by the head of their conclusion, with the term ids the prover needs: made
/// once from the spec and cloned per prover.
#[derive(Clone)]
pub struct Index {
    by_head: HashMap<TId, Vec<ThId>>,
    external: HashSet<TId>,
    ids: Ids,
}

impl Index {
    /// Index every theorem and axiom of `env` as a clause.
    pub fn new(env: &Env) -> Self {
        let t = |n: &str| env.term_id(n);
        let ids = Ids {
            lift: t("lift"),
            inst: t("inst"),
            closed: t("closed"),
            leqv: t("leqv"),
            deq: t("deq"),
            add: t("add"),
            le: t("le"),
            ls: t("ls"),
            lmax: t("lmax"),
            limax: t("limax"),
        };
        let mut ix = Index { by_head: HashMap::default(), external: [ids.deq, ids.leqv].into_iter().collect(), ids };
        for i in 0..env.thms.len() {
            ix.add_clause(env, ThId(i as u32));
        }
        ix
    }

    pub fn add_clause(&mut self, env: &Env, th: ThId) {
        let d = &env.thms[th.0 as usize];
        if let Some((t, _)) = env.head(d.concl) {
            self.by_head.entry(t).or_default().push(th);
        }
    }
}

pub struct Horn {
    ix: Index,
    /// Known facts (a lemma's hypotheses): proofs by their statement.
    pub facts: HashMap<E, P>,
    binds: Vec<Option<E>>,
    trail: Vec<u32>,
    steps: usize,
    depth: usize,
    /// The deepest failure of the current goal, for the error message.
    fail: Option<(usize, String)>,
    trace: bool,
    /// Refuse a cyclic binding (the mode checker unifies arbitrary clause heads; the
    /// prover's goals and patterns never need it).
    pub occurs_check: bool,
}

/// A solved goal whose proof is built once the search is over (`Horn::finish`).
enum Pending {
    Done(P),
    /// `inner` proves `goal` up to definitions (and the bindings made later).
    Conv { goal: E, inner: Box<Pending> },
    Clause { th: ThId, metas: Vec<E>, hyps: Vec<Pending>, goal: E },
}

const MAX_STEPS: usize = 50_000_000;
const MAX_DEPTH: usize = 20_000;

impl Horn {
    /// Index every theorem and axiom of `env` as a clause.
    pub fn new(env: &Env) -> Self { Self::with_index(Index::new(env)) }

    /// A prover over the clauses of `ix`.
    pub fn with_index(ix: Index) -> Self {
        Horn {
            ix,
            facts: HashMap::default(),
            binds: Vec::new(),
            trail: Vec::new(),
            steps: 0,
            depth: 0,
            fail: None,
            trace: std::env::var_os("LEAN0_HORN").is_some(),
            occurs_check: false,
        }
    }

    /// Register a theorem as a clause (e.g. a block's proved `ind_wf`).
    pub fn add_clause(&mut self, env: &Env, th: ThId) { self.ix.add_clause(env, th) }

    // ---------------------------------------------------------------- metavariables

    /// A fresh metavariable (`Node::Meta`). They are allocated per top-level goal (`prove`,
    /// `apply`), since a clause's arguments are read only when the goal is finished.
    pub fn meta(&mut self, env: &mut Env) -> E {
        let i = self.binds.len();
        self.binds.push(None);
        env.meta(i as u32)
    }

    fn meta_index(env: &Env, e: E) -> Option<usize> {
        match env.node(e) {
            Node::Meta(j) => Some(j as usize),
            _ => None,
        }
    }

    fn deref(&self, env: &Env, mut e: E) -> E {
        while let Some(i) = Self::meta_index(env, e) {
            match self.binds[i] {
                Some(b) => e = b,
                None => break,
            }
        }
        e
    }

    fn bind(&mut self, i: usize, e: E) {
        self.binds[i] = Some(e);
        self.trail.push(i as u32);
    }

    fn undo(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let i = self.trail.pop().unwrap();
            self.binds[i as usize] = None;
        }
    }

    /// The bindings' state, for [`Horn::restore`] (the mode checker's own search).
    pub fn save(&self) -> (usize, usize) { (self.trail.len(), self.binds.len()) }

    /// Undo the bindings and forget the metavariables made since `save`.
    pub fn restore(&mut self, (mark, nmeta): (usize, usize)) {
        self.undo(mark);
        self.binds.truncate(nmeta);
    }

    /// `e` with its bound metavariables replaced (unbound ones stay).
    pub fn zonk(&mut self, env: &mut Env, e: E) -> E {
        let mut memo = HashMap::default();
        self.zonk_aux(env, e, &mut memo)
    }

    fn zonk_aux(&mut self, env: &mut Env, e: E, memo: &mut HashMap<E, E>) -> E {
        let e = self.deref(env, e);
        if let Some(&r) = memo.get(&e) {
            return r
        }
        let r = match env.node(e) {
            Node::Var(_) | Node::Meta(_) => e,
            Node::App(t, xs) => {
                let xs = xs.to_vec();
                let ys: Vec<E> = xs.iter().map(|&x| self.zonk_aux(env, x, memo)).collect();
                if ys == xs { e } else { env.app(t, &ys) }
            }
        };
        memo.insert(e, r);
        r
    }

    pub fn is_ground(&self, env: &Env, e: E) -> bool {
        let e = self.deref(env, e);
        match env.node(e) {
            Node::Var(_) => true,
            Node::Meta(_) => false,
            Node::App(_, xs) => xs.to_vec().iter().all(|&x| self.is_ground(env, x)),
        }
    }

    /// Unify, binding metavariables on either side. Unfolds a public definition whose head
    /// meets a different head.
    pub fn unify(&mut self, env: &mut Env, a: E, b: E) -> bool {
        let a = self.deref(env, a);
        let b = self.deref(env, b);
        if a == b {
            return true
        }
        if let Some(i) = Self::meta_index(env, a) {
            if self.occurs_check && self.occurs(env, i, b) {
                return false
            }
            self.bind(i, b);
            return true
        }
        if let Some(i) = Self::meta_index(env, b) {
            if self.occurs_check && self.occurs(env, i, a) {
                return false
            }
            self.bind(i, a);
            return true
        }
        match (env.node(a), env.node(b)) {
            (Node::App(ta, xs), Node::App(tb, ys)) => {
                if ta == tb {
                    let (xs, ys) = (xs.to_vec(), ys.to_vec());
                    return xs.iter().zip(&ys).all(|(&x, &y)| self.unify(env, x, y))
                }
                if Self::public_def(env, ta) {
                    let a2 = env.unfold(a).unwrap();
                    return self.unify(env, a2, b)
                }
                if Self::public_def(env, tb) {
                    let b2 = env.unfold(b).unwrap();
                    return self.unify(env, a, b2)
                }
                false
            }
            _ => false,
        }
    }

    fn occurs(&self, env: &Env, i: usize, e: E) -> bool {
        let e = self.deref(env, e);
        match env.node(e) {
            Node::Meta(j) => j as usize == i,
            Node::Var(_) => false,
            Node::App(_, xs) => xs.to_vec().iter().any(|&x| self.occurs(env, i, x)),
        }
    }

    fn public_def(env: &Env, t: TId) -> bool {
        matches!(env.terms[t.0 as usize].kind, TermKind::Def { public_body: true, .. })
    }

    // ---------------------------------------------------------------- search

    /// Prove `goal`. The result's conclusion is `goal` with its metavariables resolved
    /// (`zonk`), up to definitions.
    pub fn prove(&mut self, env: &mut Env, lean: &mut Lean, lv: &mut Levels, hooks: &mut dyn Hooks, goal: E) -> Result<P> {
        self.start();
        let r = self.solve(env, lean, lv, hooks, goal).and_then(|pd| self.finish(env, pd));
        match r {
            Ok(p) => Ok(p),
            Err(e) => {
                let g = self.zonk(env, goal);
                let deepest = self.fail.take().map(|(_, m)| format!("\n  deepest failure: {m}")).unwrap_or_default();
                bail!("horn: cannot prove {}: {}{}", env.show(g, &[]), e.0, deepest)
            }
        }
    }

    /// Prove `goal` with the one clause `th` (for heads that are not searched, such as
    /// `deq`: the typing axioms of the schema).
    pub fn apply(&mut self, env: &mut Env, lean: &mut Lean, lv: &mut Levels, hooks: &mut dyn Hooks, th: ThId, goal: E) -> Result<P> {
        self.start();
        let r = self.try_clause(env, lean, lv, hooks, th, goal).and_then(|pd| self.finish(env, pd));
        match r {
            Ok(p) => Ok(p),
            Err(e) => {
                let g = self.zonk(env, goal);
                let deepest = self.fail.take().map(|(_, m)| format!("\n  deepest failure: {m}")).unwrap_or_default();
                bail!("horn: cannot prove {} by {}: {}{}", env.show(g, &[]), env.thm_label(th), e.0, deepest)
            }
        }
    }

    /// A top-level goal starts: its metavariables are fresh (the goal itself must not mention
    /// metavariables of an earlier goal).
    fn start(&mut self) {
        self.steps = 0;
        self.depth = 0;
        self.fail = None;
        self.binds.clear();
        self.trail.clear();
    }

    fn note_fail(&mut self, env: &mut Env, goal: E, why: &str) {
        let d = self.depth;
        if self.fail.as_ref().is_none_or(|(fd, _)| d >= *fd) {
            let g = self.zonk(env, goal);
            self.fail = Some((d, format!("{} ({why}) at depth {d}", env.show(g, &[]))));
        }
    }

    /// Build the proof of a solved goal, once every metavariable is bound: a clause's
    /// arguments may be determined only by premises after the ones that mention them.
    fn finish(&mut self, env: &mut Env, pd: Pending) -> Result<P> {
        match pd {
            Pending::Done(p) => Ok(p),
            Pending::Conv { goal, inner } => {
                let p = self.finish(env, *inner)?;
                let g = self.zonk(env, goal);
                env.convert(p, g)
            }
            Pending::Clause { th, metas, hyps, goal } => {
                let hyps: Vec<P> = hyps.into_iter().map(|h| self.finish(env, h)).collect::<Result<_>>()?;
                let d = &env.thms[th.0 as usize];
                let names: Vec<String> = d.args.iter().map(|a| a.0.clone()).collect();
                let name = d.name.clone();
                let mut args = Vec::with_capacity(metas.len());
                for (&m, n) in metas.iter().zip(&names) {
                    let v = self.zonk(env, m);
                    if !self.is_ground(env, v) {
                        bail!("{name}: variable {n} is not determined")
                    }
                    args.push(v);
                }
                let p = env.thm(th, &args, &hyps)?;
                let g = self.zonk(env, goal);
                env.convert(p, g)
            }
        }
    }

    fn solve(&mut self, env: &mut Env, lean: &mut Lean, lv: &mut Levels, hooks: &mut dyn Hooks, goal: E) -> Result<Pending> {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            bail!("too many steps")
        }
        if self.depth > MAX_DEPTH {
            bail!("too deep")
        }
        let goal = self.deref(env, goal);
        if self.trace {
            let g = self.zonk(env, goal);
            eprintln!("{:indent$}? {}", "", env.show(g, &[]), indent = self.depth.min(60));
        }
        let Some((head, _)) = env.head(goal) else { bail!("goal is a variable") };
        if !self.facts.is_empty() {
            if self.is_ground(env, goal) {
                let g = self.zonk(env, goal);
                if let Some(&p) = self.facts.get(&g) {
                    return Ok(Pending::Done(p))
                }
            } else {
                // a fact may determine the goal's metavariables (`deq G e e2 ?S`)
                let facts: Vec<(E, P)> = self.facts.iter().filter(|(f, _)| env.head(**f).is_some_and(|(t, _)| t == head)).map(|(&f, &p)| (f, p)).collect();
                for (f, p) in facts {
                    let mark = self.trail.len();
                    if self.unify(env, goal, f) {
                        return Ok(Pending::Done(p))
                    }
                    self.undo(mark);
                }
            }
        }
        let finish = |this: &mut Self, env: &mut Env, r: Result<P>| match r {
            Ok(p) => Ok(Pending::Conv { goal, inner: Box::new(Pending::Done(p)) }),
            Err(e) => {
                this.note_fail(env, goal, &e.0);
                Err(e)
            }
        };
        if let Some(r) = self.builtin(env, lean, lv, goal) {
            return finish(self, env, r)
        }
        if let Some(r) = hooks.prove(self, env, lean, lv, goal) {
            return finish(self, env, r)
        }
        if self.ix.external.contains(&head) {
            self.note_fail(env, goal, "no hook proved it");
            bail!("{}: not provable by clauses", env.terms[head.0 as usize].name)
        }
        let clauses = self.ix.by_head.get(&head).cloned().unwrap_or_default();
        for th in clauses {
            if let Ok(p) = self.try_clause(env, lean, lv, hooks, th, goal) {
                return Ok(p)
            }
        }
        // a goal whose head is a definition (`lt`): prove the unfolding
        if Self::public_def(env, head) {
            let g2 = env.unfold(goal).unwrap();
            self.depth += 1;
            let r = self.solve(env, lean, lv, hooks, g2);
            self.depth -= 1;
            return match r {
                Ok(pd) => Ok(Pending::Conv { goal, inner: Box::new(pd) }),
                Err(e) => {
                    self.note_fail(env, goal, &e.0);
                    Err(e)
                }
            }
        }
        self.note_fail(env, goal, "no clause applies");
        bail!("no clause for {}", env.terms[head.0 as usize].name)
    }

    /// Apply the clause `th` to `goal`: unify its conclusion, prove its premises. On failure
    /// the bindings are undone.
    fn try_clause(&mut self, env: &mut Env, lean: &mut Lean, lv: &mut Levels, hooks: &mut dyn Hooks, th: ThId, goal: E) -> Result<Pending> {
        let mark = self.trail.len();
        let nmeta = self.binds.len();
        let d = env.thms[th.0 as usize].clone();
        let metas: Vec<E> = (0..d.args.len()).map(|_| self.meta(env)).collect();
        let concl = env.subst(d.concl, &metas);
        let r = (|| {
            if !self.unify(env, concl, goal) {
                bail!("{}: conclusion does not match", d.name)
            }
            let mut hyps = Vec::with_capacity(d.hyps.len());
            self.depth += 1;
            for &h in d.hyps.iter() {
                let hg = env.subst(h, &metas);
                match self.solve(env, lean, lv, hooks, hg) {
                    Ok(p) => hyps.push(p),
                    Err(e) => {
                        self.depth -= 1;
                        return Err(e)
                    }
                }
            }
            self.depth -= 1;
            Ok(Pending::Clause { th, metas, hyps, goal })
        })();
        if r.is_err() {
            self.undo(mark);
            self.binds.truncate(nmeta);
        }
        r
    }

    /// `leqv a b` from the facts (a lemma's level hypotheses) by congruence, else by the
    /// level engine.
    pub fn leqv(&mut self, env: &mut Env, lean: &Lean, lv: &mut Levels, a: E, b: E) -> Result<P> {
        let (a, b) = (self.zonk(env, a), self.zonk(env, b));
        if !self.facts.is_empty() {
            let g = env.app(self.ix.ids.leqv, &[a, b]);
            if let Some(&p) = self.facts.get(&g) {
                return Ok(p)
            }
            if a != b {
                if let (Some((ta, xs)), Some((tb, ys))) = (env.head(a), env.head(b)) {
                    if ta == tb && (ta == self.ix.ids.ls || ta == self.ix.ids.lmax || ta == self.ix.ids.limax) {
                        let (xs, ys) = (xs.to_vec(), ys.to_vec());
                        let ps: Result<Vec<P>> = xs.iter().zip(&ys).map(|(&x, &y)| self.leqv(env, lean, lv, x, y)).collect();
                        if let Ok(ps) = ps {
                            let rule = if ta == self.ix.ids.ls { "leqv_succ" } else if ta == self.ix.ids.lmax { "leqv_max" } else { "leqv_imax" };
                            let mut args = Vec::new();
                            if ta == self.ix.ids.ls {
                                args.extend([xs[0], ys[0]]);
                            } else {
                                args.extend([xs[0], ys[0], xs[1], ys[1]]);
                            }
                            return env.thm_n(rule, &args, &ps)
                        }
                    }
                }
            }
        }
        lv.equiv(lean, env, a, b)
    }

    /// `lift`, `inst`, `closed` with literal indices, `leqv`, and `add`/`le` on numerals.
    fn builtin(&mut self, env: &mut Env, lean: &mut Lean, lv: &mut Levels, goal: E) -> Option<Result<P>> {
        let (t, args) = env.head(goal)?;
        // resolved throughout: a numeral may have been built around a metavariable
        let args: Vec<E> = args.to_vec();
        let args: Vec<E> = args.into_iter().map(|a| self.zonk(env, a)).collect();
        let num = |env: &Env, lean: &Lean, e: E| lean.nat_val(env, e);
        if t == self.ix.ids.lift {
            let (n, k) = (num(env, lean, args[0])?, num(env, lean, args[1])?);
            let e = args[2];
            if !self.is_ground(env, e) {
                return None
            }
            let e = self.zonk(env, e);
            return Some(lean.lift(env, n, k, e).and_then(|(e2, p)| {
                if self.unify(env, args[3], e2) { Ok(p) } else { bail!("lift: result differs") }
            }))
        }
        if t == self.ix.ids.inst {
            let k = num(env, lean, args[0])?;
            if !self.is_ground(env, args[1]) || !self.is_ground(env, args[2]) {
                return None
            }
            let (e, a) = (self.zonk(env, args[1]), self.zonk(env, args[2]));
            return Some(lean.inst(env, k, e, a).and_then(|(e2, p)| {
                if self.unify(env, args[3], e2) { Ok(p) } else { bail!("inst: result differs") }
            }))
        }
        if t == self.ix.ids.closed {
            if !self.is_ground(env, args[0]) || !self.is_ground(env, args[1]) {
                return None
            }
            let (k, e) = (self.zonk(env, args[0]), self.zonk(env, args[1]));
            return Some(lean.closed(env, k, e))
        }
        if t == self.ix.ids.leqv {
            if !self.is_ground(env, args[0]) || !self.is_ground(env, args[1]) {
                return Some(Err(Mm0Error("leqv: levels not determined".into())))
            }
            return Some(self.leqv(env, lean, lv, args[0], args[1]))
        }
        if t == self.ix.ids.add {
            if let (Some(i), Some(n)) = (num(env, lean, args[0]), num(env, lean, args[1])) {
                return Some(lean.add(env, i, n).and_then(|p| {
                    let j = lean.nat(env, i + n);
                    if self.unify(env, args[2], j) { Ok(p) } else { bail!("add: result differs") }
                }))
            }
            return None
        }
        if t == self.ix.ids.le {
            if let (Some(i), Some(n)) = (num(env, lean, args[0]), num(env, lean, args[1])) {
                return Some(lean.le(env, i, n))
            }
            return None
        }
        None
    }
}
