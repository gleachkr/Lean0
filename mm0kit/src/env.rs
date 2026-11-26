//! An MM0 environment: sorts, term constructors, definitions and theorems, plus a
//! hash-consed expression arena and a proof DAG over it.
//!
//! Expressions are shared across all statements. `Var(i)` is the `i`th argument of whatever
//! statement the expression belongs to.

use rustc_hash::FxHashMap as HashMap;
use std::fmt::Write as _;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct E(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ThId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct P(pub u32);

/// A view of an expression node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Node<'a> {
    Var(u16),
    App(TId, &'a [E]),
    /// A prover's metavariable (`horn`): never in a statement or a written proof.
    Meta(u32),
}

/// A stored expression node: `head` is a term id, or `VAR | i` for the variable `i`; the
/// arguments are `Env::args[start..start + len]`. Arguments are appended in node order, so
/// the arguments of the nodes from any point on are a suffix of `Env::args`.
#[derive(Debug, Clone, Copy)]
struct NodeRec {
    head: u32,
    start: u32,
    len: u32,
}

const VAR: u32 = 1 << 31;
const META: u32 = 1 << 30;

/// SipHash: FxHash collides on similar names (`x_l94`), which would rename them.
fn name_hash(name: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::hash::DefaultHasher::new();
    name.hash(&mut h);
    h.finish()
}

fn node_hash(head: u32, args: &[E]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = rustc_hash::FxHasher::default();
    head.hash(&mut h);
    args.hash(&mut h);
    h.finish()
}

pub const SORT_PURE: u8 = 1;
pub const SORT_STRICT: u8 = 2;
pub const SORT_PROVABLE: u8 = 4;
pub const SORT_FREE: u8 = 8;

#[derive(Debug, Clone)]
pub struct SortDecl {
    pub name: String,
    pub mods: u8,
}

#[derive(Debug, Clone)]
pub enum TermKind {
    Term,
    /// A definition. `public_body` is false for a def stated without a value in the `.mm0`.
    Def { body: E, public_body: bool },
}

#[derive(Debug, Clone)]
pub struct TermDecl {
    pub name: String,
    pub args: Vec<(String, u8)>,
    pub ret: u8,
    pub kind: TermKind,
    /// Local definitions appear only in the `.mmb`.
    pub local: bool,
    pub doc: Option<String>,
}

/// Binder names and sorts. Shared: a declaration's lemmas all have its arguments.
pub type Args = std::sync::Arc<[(String, u8)]>;

/// A theorem or axiom. Boxed slices rather than `Vec`s: there are tens of millions (lemmas).
#[derive(Debug, Clone)]
pub struct ThmDecl {
    /// Emptied for a local theorem once it is written (`Env::forget_local_names`).
    pub name: Box<str>,
    pub args: Args,
    pub hyps: Box<[E]>,
    pub concl: E,
    pub axiom: bool,
    pub local: bool,
    pub proof: Option<P>,
    pub doc: Option<Box<str>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stmt {
    Sort(u8),
    Term(TId),
    Thm(ThId),
}

/// A conversion proof discharging the obligation `a =?= b`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Cp {
    Refl,
    /// Same head on both sides; one sub-proof per argument.
    Cong(Box<[Cp]>),
    /// Unfold the left side to the given expression, then prove `that =?= b`.
    UnfoldL(E, Box<Cp>),
    /// Unfold the right side to the given expression, then prove `that =?= a`.
    UnfoldR(E, Box<Cp>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pf {
    /// The `i`th hypothesis of the theorem being proved.
    Hyp(u16, E),
    Thm { thm: ThId, args: Box<[E]>, hyps: Box<[P]>, concl: E },
    /// `from` proves an expression that converts to `target` by `cp` (`target =?= concl(from)`).
    Conv { target: E, from: P, cp: Cp },
}

#[derive(Default)]
pub struct Env {
    pub sorts: Vec<SortDecl>,
    pub terms: Vec<TermDecl>,
    pub thms: Vec<ThmDecl>,
    pub order: Vec<Stmt>,
    pub sort_names: HashMap<String, u8>,
    pub term_names: HashMap<String, TId>,
    /// Theorems by name, except local ones: their names are only kept unique, by hash
    /// (`local_names`; a false match only makes `has_thm` say yes to a free name).
    pub thm_names: HashMap<String, ThId>,
    local_names: std::collections::HashSet<u64, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>,
    /// Expression nodes, hash-consed: `node_map` holds every node's id, hashed by content.
    nodes: Vec<NodeRec>,
    args: Vec<E>,
    node_map: hashbrown::HashTable<E>,
    pfs: Vec<Pf>,
    pf_map: HashMap<Pf, P>,
    pf_concl: Vec<E>,
    /// If set, the number of proof nodes made with each theorem (`LEAN0_COSTS`).
    pub rule_counts: Option<Vec<u64>>,
    /// If set, each proof node's cost centre (`LEAN0_COSTS`): `cur_tag` when it was made.
    pub pf_tags: Option<Vec<u16>>,
    pub cur_tag: u16,
    /// Lemmas made by `add_thm_split` and `add_lemma`, by their conclusion and signature (see
    /// `sigs`). They are keyed by statement, not proof, because proofs are freed once written.
    split_lemmas: HashMap<(E, u32), ThId>,
    /// Interned signatures of lemmas: their arguments' sorts and their hypotheses.
    sigs: HashMap<Sig, u32>,
    /// Keys of `split_lemmas` and `sigs` added since the last `compact_nodes`.
    recent_lemmas: Vec<(E, u32)>,
    recent_sigs: Vec<Sig>,
    /// For each theorem whose conclusion mentions an abbreviation (`set_abbreviations`), the
    /// conclusion with the abbreviations unfolded.
    plain_concls: Vec<Option<E>>,
    /// Likewise the hypotheses of a theorem that mention one.
    plain_hyps: HashMap<u32, Box<[E]>>,
    /// For such a theorem, once used: the local lemma that states it unfolded (`plain_thm`).
    plain_thms: HashMap<u32, ThId>,
    /// The level prover's lemmas for the derived `imax` rules, by rule name (`level.rs`).
    pub level_lemmas: HashMap<&'static str, ThId>,
}

/// A lemma signature: argument sorts and hypotheses.
type Sig = (Box<[u8]>, Box<[E]>);

#[derive(Debug)]
pub struct Mm0Error(pub String);

impl std::fmt::Display for Mm0Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str(&self.0) }
}
impl std::error::Error for Mm0Error {}

pub type Result<A> = std::result::Result<A, Mm0Error>;

#[macro_export]
macro_rules! bail {
    ($($t:tt)*) => { return Err($crate::env::Mm0Error(format!($($t)*))) };
}

impl Env {
    pub fn new() -> Self { Self::default() }

    // ---------------------------------------------------------------- expressions

    fn rec_args(&self, r: NodeRec) -> &[E] { &self.args[r.start as usize..(r.start + r.len) as usize] }

    /// The node `head(xs)`, made if it is new.
    fn mk(&mut self, head: u32, xs: &[E]) -> E {
        let h = node_hash(head, xs);
        let (nodes, args) = (&self.nodes, &self.args);
        let same = |&e: &E| {
            let r = nodes[e.0 as usize];
            r.head == head && &args[r.start as usize..(r.start + r.len) as usize] == xs
        };
        if let Some(&e) = self.node_map.find(h, same) {
            return e
        }
        self.push_node(h, head, xs)
    }

    /// Add the node `head(xs)`, known to be new, with hash `h`.
    fn push_node(&mut self, h: u64, head: u32, xs: &[E]) -> E {
        let e = E(u32::try_from(self.nodes.len()).unwrap());
        let start = u32::try_from(self.args.len()).unwrap();
        self.nodes.push(NodeRec { head, start, len: xs.len() as u32 });
        self.args.extend_from_slice(xs);
        let (nodes, args) = (&self.nodes, &self.args);
        let rehash = |&e: &E| {
            let r = nodes[e.0 as usize];
            node_hash(r.head, &args[r.start as usize..(r.start + r.len) as usize])
        };
        self.node_map.insert_unique(h, e, rehash);
        e
    }

    pub fn var(&mut self, i: u16) -> E { self.mk(VAR | i as u32, &[]) }

    /// The metavariable `i` (see `horn`).
    pub fn meta(&mut self, i: u32) -> E {
        assert!(i < META, "too many metavariables");
        self.mk(META | i, &[])
    }

    pub fn app(&mut self, t: TId, args: &[E]) -> E {
        debug_assert_eq!(self.terms[t.0 as usize].args.len(), args.len(), "arity of {}", self.terms[t.0 as usize].name);
        self.mk(t.0, args)
    }

    /// Apply a term by name. Panics if the name is unknown: names used by the generator are fixed.
    pub fn app_n(&mut self, name: &str, args: &[E]) -> E {
        let t = self.term_id(name);
        self.app(t, args)
    }

    pub fn term_id(&self, name: &str) -> TId {
        *self.term_names.get(name).unwrap_or_else(|| panic!("unknown term {name}"))
    }

    pub fn thm_id(&self, name: &str) -> ThId {
        *self.thm_names.get(name).unwrap_or_else(|| panic!("unknown theorem {name}"))
    }

    pub fn node(&self, e: E) -> Node<'_> {
        let r = self.nodes[e.0 as usize];
        if r.head & VAR != 0 {
            Node::Var((r.head & !VAR) as u16)
        } else if r.head & META != 0 {
            Node::Meta(r.head & !META)
        } else {
            Node::App(TId(r.head), self.rec_args(r))
        }
    }

    pub fn head(&self, e: E) -> Option<(TId, &[E])> {
        match self.node(e) {
            Node::App(t, args) => Some((t, args)),
            Node::Var(_) | Node::Meta(_) => None,
        }
    }

    /// Instantiate the variables of `e` with `args`.
    pub fn subst(&mut self, e: E, args: &[E]) -> E {
        // the identity (a split lemma applied to its theorem's own variables): nothing to do,
        // and a lemma's conclusion can be large
        if args.iter().enumerate().all(|(i, &a)| matches!(self.node(a), Node::Var(j) if j as usize == i)) {
            return e
        }
        let mut memo = HashMap::default();
        self.subst_aux(e, args, &mut memo)
    }

    fn subst_aux(&mut self, e: E, args: &[E], memo: &mut HashMap<E, E>) -> E {
        if let Some(&r) = memo.get(&e) {
            return r
        }
        let r = match self.node(e) {
            Node::Var(i) => args[i as usize],
            Node::Meta(_) => e,
            Node::App(t, xs) => {
                let xs = xs.to_vec();
                let ys: Vec<E> = xs.iter().map(|&x| self.subst_aux(x, args, memo)).collect();
                self.app(t, &ys)
            }
        };
        memo.insert(e, r);
        r
    }

    /// One-step unfolding of a definition application.
    pub fn unfold(&mut self, e: E) -> Option<E> {
        let (t, args) = self.head(e)?;
        let args: Vec<E> = args.to_vec();
        match self.terms[t.0 as usize].kind {
            TermKind::Def { body, .. } => Some(self.subst(body, &args)),
            TermKind::Term => None,
        }
    }

    pub fn is_def(&self, t: TId) -> bool { matches!(self.terms[t.0 as usize].kind, TermKind::Def { .. }) }

    // ---------------------------------------------------------------- conversion

    /// Find a proof that `a` and `b` are equal up to unfolding definitions.
    pub fn conv(&mut self, a: E, b: E) -> Option<Cp> {
        if a == b {
            return Some(Cp::Refl)
        }
        let ha = self.head(a).map(|(t, _)| t);
        let hb = self.head(b).map(|(t, _)| t);
        if let (Some(ta), Some(tb)) = (ha, hb) {
            if ta == tb {
                let xs: Vec<E> = self.head(a).unwrap().1.to_vec();
                let ys: Vec<E> = self.head(b).unwrap().1.to_vec();
                let cps: Option<Vec<Cp>> = xs.iter().zip(&ys).map(|(&x, &y)| self.conv(x, y)).collect();
                if let Some(cps) = cps {
                    return Some(Cp::Cong(cps.into()))
                }
            }
        }
        // Unfold the later definition first: it may mention earlier ones, never the reverse.
        let da = ha.filter(|&t| self.is_def(t));
        let db = hb.filter(|&t| self.is_def(t));
        match (da, db) {
            (Some(ta), Some(tb)) if ta >= tb => {
                let a2 = self.unfold(a).unwrap();
                Some(Cp::UnfoldL(a2, Box::new(self.conv(a2, b)?)))
            }
            (Some(_), None) => {
                let a2 = self.unfold(a).unwrap();
                Some(Cp::UnfoldL(a2, Box::new(self.conv(a2, b)?)))
            }
            (_, Some(_)) => {
                let b2 = self.unfold(b).unwrap();
                Some(Cp::UnfoldR(b2, Box::new(self.conv(b2, a)?)))
            }
            (None, None) => None,
        }
    }

    // ---------------------------------------------------------------- proofs

    fn mk_pf(&mut self, pf: Pf, concl: E) -> P {
        if let Some(&p) = self.pf_map.get(&pf) {
            return p
        }
        let p = P(u32::try_from(self.pfs.len()).unwrap());
        if let (Some(c), Pf::Thm { thm, .. }) = (&mut self.rule_counts, &pf) {
            let i = thm.0 as usize;
            if c.len() <= i {
                c.resize(i + 1, 0);
            }
            c[i] += 1;
        }
        if let Some(t) = &mut self.pf_tags {
            t.push(self.cur_tag);
        }
        self.pfs.push(pf.clone());
        self.pf_concl.push(concl);
        self.pf_map.insert(pf, p);
        p
    }

    pub fn pf(&self, p: P) -> &Pf { &self.pfs[p.0 as usize] }

    /// `p`'s cost centre (0 if not recorded).
    pub fn pf_tag(&self, p: P) -> u16 { self.pf_tags.as_ref().map_or(0, |t| t[p.0 as usize]) }

    /// `mk_pf` for a rebuilt copy of `like`, in `like`'s cost centre.
    fn mk_pf_like(&mut self, pf: Pf, concl: E, like: P) -> P {
        let like_tag = self.pf_tag(like);
        let tag = std::mem::replace(&mut self.cur_tag, like_tag);
        let p = self.mk_pf(pf, concl);
        self.cur_tag = tag;
        p
    }

    /// Forget the proof nodes from `n` on. Statements added since must have been written out
    /// (`mmb::Writer::flush`) and their proofs dropped (`forget_proofs`); the caller must drop
    /// any other reference to the nodes.
    pub fn truncate_pfs(&mut self, n: usize) {
        for pf in self.pfs.drain(n..) {
            self.pf_map.remove(&pf);
        }
        self.pf_concl.truncate(n);
        if let Some(t) = &mut self.pf_tags {
            t.truncate(n);
        }
        // A large declaration leaves these at its size: give the memory back.
        if self.pfs.capacity() > (1 << 20).max(4 * n) {
            self.pfs.shrink_to_fit();
            self.pf_map.shrink_to_fit();
            self.pf_concl.shrink_to_fit();
        }
    }

    /// Drop the proofs of the statements `order[from..]` (once written out).
    pub fn forget_proofs(&mut self, from: usize) {
        for i in from..self.order.len() {
            if let Stmt::Thm(t) = self.order[i] {
                self.thms[t.0 as usize].proof = None;
            }
        }
    }

    /// The number of distinct proof nodes in `p`, counting at most `cap`.
    pub fn pf_size(&self, p: P, cap: usize) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![p];
        while let Some(p) = stack.pop() {
            if seen.len() >= cap {
                break
            }
            if !seen.insert(p) {
                continue
            }
            match self.pf(p) {
                Pf::Hyp(..) => {}
                Pf::Thm { hyps, .. } => stack.extend(hyps.iter()),
                Pf::Conv { from, .. } => stack.push(*from),
            }
        }
        seen.len()
    }

    pub fn concl(&self, p: P) -> E { self.pf_concl[p.0 as usize] }

    pub fn hyp(&mut self, i: u16, e: E) -> P { self.mk_pf(Pf::Hyp(i, e), e) }

    /// Apply a theorem. Each hypothesis proof must prove the instantiated hypothesis, up to
    /// unfolding definitions (a conversion step is inserted when needed).
    pub fn thm(&mut self, thm: ThId, args: &[E], hyps: &[P]) -> Result<P> {
        let decl = &self.thms[thm.0 as usize];
        if decl.args.len() != args.len() || decl.hyps.len() != hyps.len() {
            bail!("{}: expected {} args and {} hyps, got {} and {}", self.thm_label(thm), decl.args.len(), decl.hyps.len(), args.len(), hyps.len())
        }
        let thm = self.plain_thm(thm)?;
        let decl = &self.thms[thm.0 as usize];
        let pat_hyps = decl.hyps.clone();
        let pat_concl = decl.concl;
        let mut hs = Vec::with_capacity(hyps.len());
        for (i, (&h, &pat)) in hyps.iter().zip(&pat_hyps).enumerate() {
            let want = self.subst(pat, args);
            hs.push(self.convert(h, want).map_err(|e| {
                Mm0Error(format!("hypothesis {} of {}: {}", i + 1, self.thm_label(thm), e.0))
            })?);
        }
        let concl = self.subst(pat_concl, args);
        let p = self.mk_pf(Pf::Thm { thm, args: args.into(), hyps: hs.into(), concl }, concl);
        let plain = self.plain_concl(thm);
        if plain == pat_concl {
            return Ok(p)
        }
        let target = self.subst(plain, args);
        self.convert(p, target)
    }

    /// For a theorem whose statement mentions an abbreviation: a local lemma with the same
    /// arguments that states it with the abbreviations unfolded (made at its first use, from
    /// the theorem by conversions), so that each use needs no conversion. Else the theorem.
    fn plain_thm(&mut self, thm: ThId) -> Result<ThId> {
        let plain = self.plain_concl(thm);
        let d = &self.thms[thm.0 as usize];
        if plain == d.concl && !self.plain_hyps.contains_key(&thm.0) {
            return Ok(thm)
        }
        if let Some(&id) = self.plain_thms.get(&thm.0) {
            return Ok(id)
        }
        let (args, hyps, concl) = (d.args.clone(), d.hyps.clone(), d.concl);
        let name = format!("{}plain_{}", crate::lean::FACT_PREFIX, d.name);
        let plain_hyps = self.plain_hyps(thm);
        let vars: Vec<E> = (0..args.len()).map(|i| self.var(i as u16)).collect();
        let mut hs = Vec::with_capacity(hyps.len());
        for (i, (&h, &want)) in plain_hyps.iter().zip(hyps.iter()).enumerate() {
            let p = self.hyp(i as u16, h);
            hs.push(self.convert(p, want)?);
        }
        let p = self.mk_pf(Pf::Thm { thm, args: vars.into(), hyps: hs.into(), concl }, concl);
        let proof = self.convert(p, plain)?;
        let decl = ThmDecl { name: name.into(), args, hyps: plain_hyps, concl: plain, axiom: false, local: true, proof: Some(proof), doc: None };
        let id = self.add_thm(decl)?;
        self.plain_thms.insert(thm.0, id);
        Ok(id)
    }

    /// A theorem's conclusion with the abbreviations unfolded, as `thm` proves it.
    pub fn plain_concl(&self, thm: ThId) -> E {
        self.plain_concls.get(thm.0 as usize).copied().flatten().unwrap_or(self.thms[thm.0 as usize].concl)
    }

    /// Treat the definitions `defs` as abbreviations (the spec's numerals): a theorem declared
    /// so far whose conclusion mentions one is applied with its conclusion unfolded (`thm`
    /// adds the conversion), so that proofs work with the unfolded forms only.
    pub fn set_abbreviations(&mut self, defs: &[TId]) {
        self.plain_concls = (0..self.thms.len())
            .map(|i| {
                let c = self.thms[i].concl;
                let c2 = self.expand(c, defs);
                (c2 != c).then_some(c2)
            })
            .collect();
        self.plain_hyps.clear();
        for i in 0..self.thms.len() {
            let hyps = self.thms[i].hyps.clone();
            let plain: Box<[E]> = hyps.iter().map(|&h| self.expand(h, defs)).collect();
            if plain != hyps {
                self.plain_hyps.insert(i as u32, plain);
            }
        }
    }

    /// A theorem's hypotheses with the abbreviations unfolded (`thm` accepts proofs of them).
    pub fn plain_hyps(&self, thm: ThId) -> Box<[E]> {
        self.plain_hyps.get(&thm.0).cloned().unwrap_or_else(|| self.thms[thm.0 as usize].hyps.clone())
    }

    /// Rewrite every statement declared so far with the definitions `defs` unfolded, in its
    /// hypotheses too (for an analysis of the statements, not for proofs).
    pub fn unfold_in_statements(&mut self, defs: &[TId]) {
        for i in 0..self.thms.len() {
            let hyps: Vec<E> = self.thms[i].hyps.to_vec().into_iter().map(|h| self.expand(h, defs)).collect();
            let concl = self.thms[i].concl;
            self.thms[i].concl = self.expand(concl, defs);
            self.thms[i].hyps = hyps.into();
        }
    }

    /// `e` with the definitions `defs` unfolded (a statement: a small tree).
    fn expand(&mut self, e: E, defs: &[TId]) -> E {
        let Node::App(t, xs) = self.node(e) else { return e };
        let xs: Vec<E> = xs.to_vec().into_iter().map(|x| self.expand(x, defs)).collect();
        let e2 = self.app(t, &xs);
        if defs.contains(&t) {
            let u = self.unfold(e2).unwrap();
            self.expand(u, defs)
        } else {
            e2
        }
    }

    pub fn thm_n(&mut self, name: &str, args: &[E], hyps: &[P]) -> Result<P> {
        let t = self.thm_id(name);
        self.thm(t, args, hyps)
    }

    /// Turn a proof of `concl(p)` into a proof of `target`, by unfolding definitions.
    pub fn convert(&mut self, p: P, target: E) -> Result<P> {
        let have = self.concl(p);
        if have == target {
            return Ok(p)
        }
        match self.conv(target, have) {
            Some(cp) => Ok(self.mk_pf(Pf::Conv { target, from: p, cp }, target)),
            None => bail!("not convertible:\n  want {}\n  have {}", self.show(target, &[]), self.show(have, &[])),
        }
    }

    // ---------------------------------------------------------------- declarations

    pub fn add_sort(&mut self, name: &str, mods: u8) -> Result<u8> {
        if self.sort_names.contains_key(name) {
            bail!("duplicate sort {name}")
        }
        let id = u8::try_from(self.sorts.len()).map_err(|_| Mm0Error("too many sorts".into()))?;
        self.sorts.push(SortDecl { name: name.into(), mods });
        self.sort_names.insert(name.into(), id);
        self.order.push(Stmt::Sort(id));
        Ok(id)
    }

    pub fn add_term(&mut self, decl: TermDecl) -> Result<TId> {
        if self.term_names.contains_key(&decl.name) {
            bail!("duplicate term {}", decl.name)
        }
        let id = TId(u32::try_from(self.terms.len()).unwrap());
        self.term_names.insert(decl.name.clone(), id);
        self.terms.push(decl);
        self.order.push(Stmt::Term(id));
        Ok(id)
    }

    pub fn add_thm(&mut self, decl: ThmDecl) -> Result<ThId> {
        if self.has_thm(&decl.name) {
            bail!("duplicate theorem {}", decl.name)
        }
        if decl.axiom && decl.proof.is_some() {
            bail!("axiom {} with a proof", decl.name)
        }
        let id = ThId(u32::try_from(self.thms.len()).unwrap());
        if decl.local {
            self.local_names.insert(name_hash(&decl.name));
        } else {
            self.thm_names.insert(decl.name.to_string(), id);
        }
        self.thms.push(decl);
        self.order.push(Stmt::Thm(id));
        Ok(id)
    }

    /// Add a theorem, first moving parts of a large proof into local lemmas (named
    /// `name_l1`, ...), so that no single theorem exceeds a verifier's per-theorem heap.
    /// Each lemma has the theorem's arguments and hypotheses. A sub-proof used more than once
    /// becomes a lemma if it is not tiny, and the remaining tree of each proof that is written
    /// out is bounded by `budget` (estimated proof steps plus their arguments). A sub-proof
    /// whose conclusion an earlier lemma with the same argument sorts and hypotheses proves is
    /// replaced by that lemma.
    pub fn add_thm_split(&mut self, mut decl: ThmDecl, budget: usize) -> Result<ThId> {
        if let Some(root) = decl.proof {
            let sig = self.sig(&decl.args, &decl.hyps);
            let mut uses = HashMap::default();
            count_uses(self, root, sig, &mut uses);
            let mut sp = Splitter { budget, memo: HashMap::default(), uses, lemmas: 0, decl: &decl, sig, root };
            let (p, _) = sp.go(self, root)?;
            decl.proof = Some(p);
        }
        self.add_thm(decl)
    }

    /// A local lemma without hypotheses proved by `proof`: an earlier one with the same
    /// conclusion and argument sorts if there is one, else a new one (`add_thm_split`) named
    /// `name`.
    pub fn add_lemma(&mut self, name: &str, args: Args, proof: P, budget: usize) -> Result<ThId> {
        let key = (self.concl(proof), self.sig(&args, &[]));
        if let Some(&id) = self.split_lemmas.get(&key) {
            return Ok(id)
        }
        let concl = self.concl(proof);
        let decl = ThmDecl { name: name.into(), args, hyps: Box::new([]), concl, axiom: false, local: true, proof: Some(proof), doc: None };
        let id = self.add_thm_split(decl, budget)?;
        self.add_split_lemma(key, id);
        Ok(id)
    }

    /// The id of a lemma signature: argument sorts and hypotheses.
    fn sig(&mut self, args: &[(String, u8)], hyps: &[E]) -> u32 {
        let key: Sig = (args.iter().map(|a| a.1).collect(), hyps.into());
        if let Some(&i) = self.sigs.get(&key) {
            return i
        }
        let n = self.sigs.len() as u32;
        self.recent_sigs.push(key.clone());
        self.sigs.insert(key, n);
        n
    }

    fn add_split_lemma(&mut self, key: (E, u32), id: ThId) {
        self.recent_lemmas.push(key);
        self.split_lemmas.insert(key, id);
    }

    /// Forget the expression nodes from `n` on that neither the statements `order[from..]` nor
    /// `roots` use, and renumber the rest (in order, so arguments still come before the terms
    /// using them). No proof may still mention a node from `n` on (`truncate_pfs`). Returns the
    /// new number of each kept node from `n` on; any other node from `n` on is gone, and the
    /// caller must drop its references to it.

    pub fn compact_nodes(&mut self, n: usize, from: usize, roots: &[E]) -> HashMap<E, E> {
        let mut keep = vec![false; self.nodes.len() - n];
        let mut stack = roots.to_vec();
        // lemma signatures mention hypotheses, which must keep their numbers' meaning
        for (_, hyps) in &self.recent_sigs {
            stack.extend(hyps.iter());
        }
        for &st in &self.order[from..] {
            match st {
                Stmt::Thm(t) => {
                    let d = &self.thms[t.0 as usize];
                    stack.extend(&d.hyps);
                    stack.push(d.concl);
                }
                Stmt::Term(t) => {
                    if let TermKind::Def { body, .. } = self.terms[t.0 as usize].kind {
                        stack.push(body);
                    }
                }
                Stmt::Sort(_) => {}
            }
        }
        while let Some(e) = stack.pop() {
            let i = e.0 as usize;
            if i < n || keep[i - n] {
                continue
            }
            keep[i - n] = true;
            if let Node::App(_, args) = self.node(e) {
                stack.extend(args.iter());
            }
        }
        let old: Vec<NodeRec> = self.nodes.drain(n..).collect();
        let base = old.first().map_or(self.args.len(), |r| r.start as usize);
        let old_args = self.args.split_off(base);
        let old_xs = |r: &NodeRec| &old_args[r.start as usize - base..(r.start + r.len) as usize - base];
        for (j, r) in old.iter().enumerate() {
            if let Ok(entry) = self.node_map.find_entry(node_hash(r.head, old_xs(r)), |&e| e.0 as usize == n + j) {
                entry.remove();
            }
        }
        let mut map = HashMap::default();
        for (j, r) in old.iter().enumerate() {
            if !keep[j] {
                continue
            }
            // renumbering is injective, so the node is still new
            let xs: Vec<E> = old_xs(r).iter().map(|a| *map.get(a).unwrap_or(a)).collect();
            let e = self.push_node(node_hash(r.head, &xs), r.head, &xs);
            map.insert(E((n + j) as u32), e);
        }
        let f = |e: &mut E| {
            if let Some(&e2) = map.get(e) {
                *e = e2
            }
        };
        for i in from..self.order.len() {
            match self.order[i] {
                Stmt::Thm(t) => {
                    let d = &mut self.thms[t.0 as usize];
                    d.hyps.iter_mut().for_each(f);
                    f(&mut d.concl);
                }
                Stmt::Term(t) => {
                    if let TermKind::Def { body, .. } = &mut self.terms[t.0 as usize].kind {
                        f(body);
                    }
                }
                Stmt::Sort(_) => {}
            }
        }
        // Take out every renumbered key before inserting any: a new number may be another
        // key's old one.
        let kept: Vec<_> = std::mem::take(&mut self.recent_lemmas)
            .into_iter()
            .filter_map(|k| self.split_lemmas.remove(&k).map(|id| (k, id)))
            .collect();
        for ((mut e, sig), id) in kept {
            f(&mut e);
            self.split_lemmas.insert((e, sig), id);
        }
        let sigs: Vec<_> = std::mem::take(&mut self.recent_sigs).into_iter().filter_map(|k| self.sigs.remove(&k).map(|i| (k, i))).collect();
        for ((sorts, mut hyps), i) in sigs {
            hyps.iter_mut().for_each(f);
            self.sigs.insert((sorts, hyps), i);
        }
        map
    }

    pub fn has_term(&self, name: &str) -> bool { self.term_names.contains_key(name) }
    pub fn has_thm(&self, name: &str) -> bool { self.thm_names.contains_key(name) || self.local_names.contains(&name_hash(name)) }

    /// Take back the statements `order[from..]` (none of them written yet) and their names.
    /// Proof nodes are not freed here (`forget_proofs`).
    pub fn rollback(&mut self, from: usize) {
        let mut nterms = self.terms.len();
        let mut nthms = self.thms.len();
        for &st in &self.order[from..] {
            match st {
                Stmt::Sort(_) => panic!("rollback over a sort"),
                Stmt::Term(t) => nterms = nterms.min(t.0 as usize),
                Stmt::Thm(t) => nthms = nthms.min(t.0 as usize),
            }
        }
        for d in &self.terms[nterms..] {
            self.term_names.remove(&d.name);
        }
        for d in &self.thms[nthms..] {
            if d.local {
                self.local_names.remove(&name_hash(&d.name));
            } else {
                self.thm_names.remove(&*d.name);
            }
        }
        self.terms.truncate(nterms);
        self.thms.truncate(nthms);
        self.order.truncate(from);
        self.split_lemmas.retain(|_, id| (id.0 as usize) < nthms);
        self.plain_thms.retain(|_, id| (id.0 as usize) < nthms);
        self.level_lemmas.retain(|_, id| (id.0 as usize) < nthms);
        let keep = self.split_lemmas.clone();
        self.recent_lemmas.retain(|k| keep.contains_key(k));
    }

    /// Free the names of the local theorems among `order[from..]`, which must have been
    /// written (`mmb::Writer::flush` streams the names into the index).
    pub fn forget_local_names(&mut self, from: usize) {
        for &st in &self.order[from..] {
            if let Stmt::Thm(t) = st {
                let d = &mut self.thms[t.0 as usize];
                if d.local {
                    d.name = "".into();
                }
            }
        }
    }

    /// A theorem's name for messages.
    pub fn thm_label(&self, t: ThId) -> String {
        match &self.thms[t.0 as usize].name {
            n if n.is_empty() => format!("local theorem #{}", t.0),
            n => n.to_string(),
        }
    }

    // ---------------------------------------------------------------- printing

    /// Print an expression in MM0 math syntax (prefix applications, no notation).
    pub fn show(&self, e: E, vars: &[&str]) -> String {
        let mut s = String::new();
        self.show_aux(e, vars, false, &mut s);
        s
    }

    fn show_aux(&self, e: E, vars: &[&str], paren: bool, out: &mut String) {
        match self.node(e) {
            Node::Meta(i) => out.push_str(&format!("?m{i}")),
            Node::Var(i) => match vars.get(i as usize) {
                Some(n) => out.push_str(n),
                None => write!(out, "?v{i}").unwrap(),
            },
            Node::App(t, args) => {
                let name = &self.terms[t.0 as usize].name;
                if args.is_empty() {
                    out.push_str(name);
                    return
                }
                if paren {
                    out.push('(');
                }
                out.push_str(name);
                for &a in args.iter() {
                    out.push(' ');
                    self.show_aux(a, vars, true, out);
                }
                if paren {
                    out.push(')');
                }
            }
        }
    }

    fn binders(&self, args: &[(String, u8)], out: &mut String) {
        let mut i = 0;
        while i < args.len() {
            let s = args[i].1;
            let mut j = i;
            out.push_str(" (");
            while j < args.len() && args[j].1 == s {
                if j > i {
                    out.push(' ');
                }
                out.push_str(&args[j].0);
                j += 1;
            }
            write!(out, ": {})", self.sorts[s as usize].name).unwrap();
            i = j;
        }
    }

    fn doc(doc: Option<&str>, out: &mut String) {
        if let Some(d) = doc {
            for line in d.lines() {
                writeln!(out, "--| {line}").unwrap();
            }
        }
    }

    /// The `.mm0` text of a public statement (`None` for local ones).
    pub fn stmt_text(&self, st: Stmt) -> Option<String> {
        let mut out = String::new();
        match st {
            Stmt::Sort(s) => {
                let d = &self.sorts[s as usize];
                for (bit, kw) in [(SORT_PURE, "pure "), (SORT_STRICT, "strict "), (SORT_PROVABLE, "provable "), (SORT_FREE, "free ")] {
                    if d.mods & bit != 0 {
                        out.push_str(kw);
                    }
                }
                writeln!(out, "sort {};", d.name).unwrap();
            }
            Stmt::Term(t) => {
                let d = &self.terms[t.0 as usize];
                if d.local {
                    return None
                }
                Self::doc(d.doc.as_deref(), &mut out);
                let names: Vec<&str> = d.args.iter().map(|a| a.0.as_str()).collect();
                match d.kind {
                    TermKind::Term => out.push_str("term "),
                    TermKind::Def { .. } => out.push_str("def "),
                }
                out.push_str(&d.name);
                self.binders(&d.args, &mut out);
                write!(out, ": {}", self.sorts[d.ret as usize].name).unwrap();
                if let TermKind::Def { body, public_body: true } = d.kind {
                    write!(out, " = $ {} $", self.show(body, &names)).unwrap();
                }
                out.push_str(";\n");
            }
            Stmt::Thm(t) => {
                let d = &self.thms[t.0 as usize];
                if d.local {
                    return None
                }
                Self::doc(d.doc.as_deref(), &mut out);
                let names: Vec<&str> = d.args.iter().map(|a| a.0.as_str()).collect();
                out.push_str(if d.axiom { "axiom " } else { "theorem " });
                out.push_str(&d.name);
                self.binders(&d.args, &mut out);
                out.push(':');
                for &h in &d.hyps {
                    write!(out, "\n  $ {} $ >", self.show(h, &names)).unwrap();
                }
                write!(out, "{}$ {} $;\n", if d.hyps.is_empty() { " " } else { "\n  " }, self.show(d.concl, &names)).unwrap();
            }
        }
        Some(out)
    }

    /// For each axiom and theorem, how many distinct proof steps apply it, over the proofs of
    /// all theorems in the environment.
    pub fn num_nodes(&self) -> usize { self.nodes.len() }

    /// Approximate heap bytes of the long-lived parts, by part (for memory diagnostics).
    pub fn mem_report(&self) -> Vec<(&'static str, usize)> {
        use std::mem::size_of;
        let st = |s: &String| s.capacity() + 16;
        let args = |a: &Vec<(String, u8)>| a.capacity() * size_of::<(String, u8)>() + a.iter().map(|x| st(&x.0)).sum::<usize>();
        fn names<V>(m: &HashMap<String, V>) -> usize { m.capacity() * (std::mem::size_of::<String>() + 8) + m.keys().map(|s| s.capacity() + 16).sum::<usize>() }
        vec![
            ("nodes", self.nodes.capacity() * size_of::<NodeRec>() + self.args.capacity() * 4 + self.node_map.capacity() * 5),
            ("thms", self.thms.capacity() * size_of::<ThmDecl>()),
            ("thm strings", self.thms.iter().map(|d| d.name.len() + d.hyps.len() * 4).sum()),
            ("terms", self.terms.capacity() * size_of::<TermDecl>() + self.terms.iter().map(|d| st(&d.name) + args(&d.args)).sum::<usize>()),
            ("thm_names", names(&self.thm_names)),
            ("term_names", names(&self.term_names)),
            ("pfs", self.pfs.capacity() * (size_of::<Pf>() + 4) + self.pf_map.capacity() * (size_of::<Pf>() + 5)),
            ("lemma tables", self.split_lemmas.capacity() * 13 + self.sigs.capacity() * 40),
            ("order", self.order.capacity() * size_of::<Stmt>()),
        ]
    }
    pub fn num_pfs(&self) -> usize { self.pfs.len() }
}

/// How many times each sub-proof of `p` is used (by distinct parents, as the writer counts).
/// Count the uses of each sub-proof of `p`, not looking inside those that are already lemmas
/// for the signature `sig` (the splitter cites those as they are). Lemmas are made from
/// overlapping derivations, so walking those again for each one would take quadratic time.
fn count_uses(env: &Env, p: P, sig: u32, uses: &mut HashMap<P, u32>) {
    let root = p;
    let mut stack = vec![p];
    while let Some(p) = stack.pop() {
        let c = uses.entry(p).or_insert(0);
        *c += 1;
        if *c > 1 || (p != root && env.split_lemmas.contains_key(&(env.concl(p), sig))) {
            continue
        }
        match env.pf(p) {
            Pf::Hyp(..) => {}
            Pf::Thm { hyps, .. } => stack.extend(hyps.iter()),
            Pf::Conv { from, .. } => stack.push(*from),
        }
    }
}

/// A shared sub-proof costing more than this becomes a lemma, written once.
const SHARED_LEMMA_COST: usize = 64;

struct Splitter<'d> {
    budget: usize,
    /// Rewritten proofs and their estimated cost, with lemmas counted as one step.
    memo: HashMap<P, (P, usize)>,
    uses: HashMap<P, u32>,
    lemmas: usize,
    decl: &'d ThmDecl,
    /// The theorem's signature (`Env::sig`).
    sig: u32,
    root: P,
}

impl Splitter<'_> {
    /// The rewritten proof and its estimated cost (counting unshared sub-proofs once per use).
    fn go(&mut self, env: &mut Env, p: P) -> Result<(P, usize)> {
        if let Some(&r) = self.memo.get(&p) {
            return Ok(r)
        }
        if let Some(&id) = env.split_lemmas.get(&(env.concl(p), self.sig)) {
            let r = (self.instance(env, id)?, self.small());
            self.memo.insert(p, r);
            return Ok(r)
        }
        let (np, cost) = match env.pf(p).clone() {
            Pf::Hyp(..) => (p, 1),
            Pf::Thm { thm, args, hyps, concl } => {
                let mut kids = Vec::with_capacity(hyps.len());
                for &h in hyps.iter() {
                    kids.push(self.go(env, h)?);
                }
                let own = 2 + args.len();
                self.shrink(env, &mut kids, own)?;
                let total = own + kids.iter().map(|k| k.1).sum::<usize>();
                let hs: Vec<P> = kids.iter().map(|k| k.0).collect();
                let np = if hs.as_slice() == &*hyps { p } else { env.mk_pf_like(Pf::Thm { thm, args, hyps: hs.into(), concl }, concl, p) };
                (np, total)
            }
            Pf::Conv { target, from, cp } => {
                let mut kids = vec![self.go(env, from)?];
                self.shrink(env, &mut kids, 2)?;
                let (f, c) = kids[0];
                let np = if f == from { p } else { env.mk_pf_like(Pf::Conv { target, from: f, cp }, target, p) };
                (np, c + 2)
            }
        };
        let r = if p != self.root && self.uses[&p] > 1 && cost > SHARED_LEMMA_COST {
            (self.lemma(env, np)?, self.small())
        } else {
            (np, cost)
        };
        self.memo.insert(p, r);
        Ok(r)
    }

    /// The cost of using a lemma.
    fn small(&self) -> usize { 3 + self.decl.args.len() + self.decl.hyps.len() }

    /// Move the costliest sub-proofs into lemmas until the node fits the budget.
    fn shrink(&mut self, env: &mut Env, kids: &mut [(P, usize)], own: usize) -> Result<()> {
        let small = self.small();
        loop {
            let total = own + kids.iter().map(|k| k.1).sum::<usize>();
            if total <= self.budget {
                return Ok(())
            }
            let Some(i) = (0..kids.len()).filter(|&i| kids[i].1 > small).max_by_key(|&i| kids[i].1) else { return Ok(()) };
            kids[i] = (self.lemma(env, kids[i].0)?, small);
        }
    }

    /// A lemma proving `concl(p)` by `p` (or an earlier one with that conclusion), applied to
    /// the theorem's arguments and hypotheses.
    fn lemma(&mut self, env: &mut Env, p: P) -> Result<P> {
        if let Some(&id) = env.split_lemmas.get(&(env.concl(p), self.sig)) {
            return self.instance(env, id)
        }
        self.lemmas += 1;
        let prefix = if self.decl.name.starts_with(crate::lean::FACT_PREFIX) { "" } else { crate::lean::FACT_PREFIX };
        let base = format!("{prefix}{}_l{}", self.decl.name, self.lemmas);
        let mut name = base.clone();
        while env.has_thm(&name) {
            name.push('_');
        }
        let concl = env.concl(p);
        let id = env.add_thm(ThmDecl {
            name: name.into(),
            args: self.decl.args.clone(),
            hyps: self.decl.hyps.clone(),
            concl,
            axiom: false,
            local: true,
            proof: Some(p),
            doc: None,
        })?;
        env.add_split_lemma((concl, self.sig), id);
        self.instance(env, id)
    }

    fn instance(&mut self, env: &mut Env, id: ThId) -> Result<P> {
        let vars: Vec<E> = (0..self.decl.args.len()).map(|i| env.var(i as u16)).collect();
        let hyps: Vec<P> = self.decl.hyps.iter().enumerate().map(|(i, &h)| env.hyp(i as u16, h)).collect();
        env.thm(id, &vars, &hyps)
    }
}
