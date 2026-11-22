//! Certificate generation for a whole export: one MM0 constant per Lean constant, its
//! statements, and their proofs.
//!
//! Per Lean declaration `c.{us} : T`:
//!
//! - axiom: `term c (us: lvl): expr;`, `theorem c_wf: ty G T (srt u)` (proved),
//!   `axiom c_df: leqv us us' > deq G (c us) (c us') T` and `axiom c_closed: closed k (c us)`;
//! - definition `:= v`: `def c (us: lvl): expr = $ v $;` and `theorem c_ty: ty G (c us) T`;
//! - theorem `:= v`: the same, but the `.mm0` states `def c (us: lvl): expr;` without the value.
//!
//! Definitions also get a local lemma `c_closed: closed k (c us)` in the `.mmb`.

use crate::elab::{Elab, R};
use crate::names::{mangle, Names};
use crate::natlit::{self, NatLits};
use nanoda_lib::env::{Declar, DeclarInfo, DeclarMap, EnvLimit, InductiveData};
use nanoda_lib::inductive::{CtorHeader, IndTyHeader, InductiveCheckState};
use nanoda_lib::expr::Expr;
use nanoda_lib::level::Level;
use nanoda_lib::name::Name;
use nanoda_lib::tc::TypeChecker;
use nanoda_lib::util::{ExportFile, NamePtr};
use mm0kit::env::{Env, Stmt, TId, TermDecl, TermKind, ThId, ThmDecl, E};
use mm0kit::bin::Bins;
use mm0kit::lean::Lean;
use mm0kit::level::Levels;
use rustc_hash::FxHashMap as HashMap;
use std::time::Instant;

/// Proofs larger than this (estimated proof steps plus arguments) are split into local lemmas,
/// keeping each theorem well inside mm0-c's 64k-entry heap (overridden by `LEAN0_SPLIT_BUDGET`).
const SPLIT_BUDGET: usize = 6000;

pub(super) fn split_budget() -> usize {
    static B: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var("LEAN0_SPLIT_BUDGET").ok().and_then(|s| s.parse().ok()).unwrap_or(SPLIT_BUDGET))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstKind {
    /// An MM0 `term`: typed by its `c_df` axiom.
    Opaque,
    /// An MM0 `def`: typed by its `c_ty` theorem.
    Def,
    /// Type `i` of an inductive block whose data definition is the `term` (stage B): the
    /// constant is `ind_ty (X_D us) i`, typed by its `c_df` theorem.
    Ind { i: usize },
    /// Constructor `c` of type `i` of a block: `ind_ctor (X_D us) i c`.
    Ctor { i: usize, c: usize },
    /// The recursor of type `i` of a block: `ind_rec (X_D us) i v`, where `v` is its first
    /// level if `large` (the motive's), else `lz`.
    Rec { i: usize, large: bool },
}

#[derive(Debug, Clone)]
pub struct ConstInfo {
    pub term: TId,
    pub kind: ConstKind,
    pub nlevels: usize,
    pub ty_thm: ThId,
}

#[derive(Debug, Clone)]
pub struct DeclStat {
    pub name: String,
    pub kind: &'static str,
    pub ok: bool,
    pub message: String,
    pub proof_nodes: usize,
    pub type_mismatches: usize,
    pub micros: u128,
}

pub struct Gen {
    pub env: Env,
    pub lean: Lean,
    pub lv: Levels,
    pub consts: HashMap<String, ConstInfo>,
    pub(crate) terms: Names,
    pub(crate) thms: Names,
    /// Names that variables may use and constants may not.
    var_names: Names,
    spec_len: usize,
    /// The number of theorems in the spec.
    pub spec_thms: usize,
    pub stats: Vec<DeclStat>,
    /// Iota as a closed equation (`ind_iota_eq`) of the blocks certified by the schema, by
    /// (recursor, constructor).
    pub iota_eq: HashMap<(String, String), ThId>,
    /// `Quot.lift` / `Quot.ind` reduction axioms.
    pub quot_red: HashMap<String, ThId>,
    /// Structures, by inductive type name.
    pub structs: HashMap<String, StructInfo>,
    /// Block atoms (`term X_blk: blk;`), by inductive type name.
    pub blks: HashMap<String, TId>,
    /// Stage-B blocks, by the name of each of their types.
    pub blocks: HashMap<String, std::rc::Rc<crate::induct::Block>>,
    /// For the run's report: the number of blocks certified by the schema (a block it does not
    /// certify is an error).
    pub stage_b: usize,
    /// The Horn prover's index of the spec's clauses (made once; the blocks' theorems are
    /// added per declaration).
    pub horn_index: mm0kit::horn::Index,
    /// The number of the spec's terms: a term from there on is generated.
    pub spec_terms: usize,
    /// Level-congruence axioms `c_eeqv` of the opaque constants that occur in a block's data
    /// (`induct::eeqv_axioms`), by the constant's term.
    pub eeqv_axioms: HashMap<TId, ThId>,
    /// Binary numerals and the arithmetic relations' prover.
    pub bins: Bins,
    /// The literal axioms, once `Nat.zero` and `Nat.succ` are declared.
    pub nat: Option<NatLits>,
    /// The literal theorems of each accelerated operation, in the order of `natlit::OPS`.
    pub nat_ops: HashMap<String, Vec<ThId>>,
    /// The derived defining equations of the operations (`natlit::eq_ops`): `Nat_add_eqs`, ...
    pub nat_eqs: HashMap<String, ThId>,
    /// Counts for the run's report: operations whose literal theorems follow from their
    /// equations, and operations left with generated axioms, with the reason.
    pub lit_stage_b: usize,
    pub lit_stage_a: Vec<(String, String)>,
    /// Recursors declared early, with a sibling whose rules mention them: their MM0 names.
    predeclared: HashMap<String, String>,
    /// `LEAN0_COSTS`: proof nodes by elaborator rule.
    pub costs: Option<crate::costs::Costs>,
    /// Sharded generation: certify only the declarations with these indices (`lo..hi`). The ones
    /// before are replayed: their statements are made without their proofs.
    pub shard: Option<(usize, usize)>,
    /// The current declaration is replayed (see `shard`).
    pub(crate) replay: bool,
    /// Sharded generation into separate certificates (parts): a replayed theorem's proof term
    /// becomes an opaque term, since the earlier part's statements are restated as axioms.
    pub parts: bool,
    /// Where the statements of the first declaration not replayed start in `Env::order`.
    own_from: Option<usize>,
    /// The bytes written before the first declaration not replayed (in part mode, the
    /// restated statements of the earlier parts, and lemmas made while replaying).
    pub replayed_bytes: u64,
}

#[derive(Debug, Clone)]
pub struct StructInfo {
    /// The block atom (`term X_blk: blk;`).
    pub blk: TId,
    pub np: usize,
    pub nf: usize,
    /// Typing axiom of each field, and whether it takes the sort premise.
    pub df: Vec<(ThId, bool)>,
    /// For a field whose axiom takes the sort premise: a second typing axiom for projecting
    /// from a proposition, if the fields up to it can all be propositions, with the levels
    /// (over the level variables `1..`) that its premises equate to `lz`.
    pub df_prop: Vec<Option<(ThId, Vec<E>)>>,
    /// Reduction lemma of each field (`proj_mk`), with `df`'s premises of `proj_ok`, then the
    /// constructor application's `sty` and the projection's typing; `red_prop` as `df_prop`
    /// (its levels are `df_prop`'s).
    pub red: Vec<(ThId, bool)>,
    pub red_prop: Vec<Option<ThId>>,
    pub eta: Option<ThId>,
    /// The structure's sort level, over the level variables `1..`.
    pub sort: E,
    /// Each field's type, a de Bruijn term under the parameters and earlier fields, over the
    /// level variables `1..`.
    pub field_tys: Vec<E>,
}

impl Gen {
    pub fn new(spec_src: &str) -> R<Self> {
        let mut env = Env::new();
        mm0kit::parse::parse_into(&mut env, spec_src).map_err(|e| format!("spec: {}", e.0))?;
        let lean = Lean::new(&mut env);
        let bins = Bins::new(&env);
        let mut terms = Names::default();
        let mut thms = Names::default();
        for t in &env.terms {
            terms.reserve(&t.name);
        }
        for t in &env.thms {
            thms.reserve(&t.name);
        }
        // and the TG library's, so the statements also read the same after it (audit §11)
        let (tg_terms, tg_thms) = lean0_check::tg::names()?;
        for t in &tg_terms {
            terms.reserve(t);
        }
        for t in &tg_thms {
            thms.reserve(t);
        }
        let mut var_names = Names::default();
        var_names.reserve("G");
        terms.reserve("G");
        let spec_len = env.order.len();
        let spec_thms = env.thms.len();
        let spec_terms = env.terms.len();
        let horn_index = mm0kit::horn::Index::new(&env);
        let costs = crate::costs::Costs::from_env();
        if costs.is_some() {
            env.rule_counts = Some(Vec::new());
            env.pf_tags = Some(vec![0; env.num_pfs()]);
        }
        Ok(Gen {
            env,
            lean,
            lv: Levels::new(),
            consts: HashMap::default(),
            terms,
            thms,
            var_names,
            spec_len,
            spec_thms,
            stats: Vec::new(),
            iota_eq: HashMap::default(),
            quot_red: HashMap::default(),
            structs: HashMap::default(),
            blks: HashMap::default(),
            blocks: HashMap::default(),
            stage_b: 0,
            horn_index,
            spec_terms,
            eeqv_axioms: HashMap::default(),
            bins,
            nat: None,
            nat_ops: HashMap::default(),
            nat_eqs: HashMap::default(),
            lit_stage_b: 0,
            lit_stage_a: Vec::new(),
            costs,
            shard: None,
            replay: false,
            parts: false,
            own_from: None,
            replayed_bytes: 0,
            predeclared: HashMap::default(),
        })
    }

    pub fn show(&self, e: E) -> String { self.env.show(e, &[]) }

    /// The MM0 term of the Lean constant `name` at the levels `ls`.
    pub fn const_term(&mut self, name: &str, ls: &[E]) -> Option<E> {
        let ci = self.consts.get(name)?.clone();
        if ci.nlevels != ls.len() {
            return None
        }
        Some(match ci.kind {
            ConstKind::Opaque | ConstKind::Def => self.env.app(ci.term, ls),
            ConstKind::Ind { i } => {
                let d = self.env.app(ci.term, ls);
                let i = self.lean.nat(&mut self.env, i);
                self.env.app_n("ind_ty", &[d, i])
            }
            ConstKind::Ctor { i, c } => {
                let d = self.env.app(ci.term, ls);
                let (i, c) = (self.lean.nat(&mut self.env, i), self.lean.nat(&mut self.env, c));
                self.env.app_n("ind_ctor", &[d, i, c])
            }
            ConstKind::Rec { i, large } => {
                let (v, bl) = if large { (ls[0], &ls[1..]) } else { (self.env.app_n("lz", &[]), ls) };
                let d = self.env.app(ci.term, bl);
                let i = self.lean.nat(&mut self.env, i);
                self.env.app_n("ind_rec", &[d, i, v])
            }
        })
    }

    /// The atom of the block of the inductive type `ind` (`term X_blk: blk;`), declared on
    /// first use.
    pub fn blk_id(&mut self, ind: &str) -> R<TId> {
        let t = match self.blks.get(ind) {
            Some(&t) => t,
            None => {
                let name = self.terms.fresh(&format!("{}_blk", mangle(ind)));
                let blk_s = self.env.sort_names["blk"];
                let t = add_term(&mut self.env, &name, vec![], blk_s, TermKind::Term, &format!("The inductive block of `{ind}`."))?;
                self.blks.insert(ind.to_string(), t);
                t
            }
        };
        Ok(t)
    }

    /// The block atom of `ind` as a term.
    pub fn blk_term(&mut self, ind: &str) -> R<E> {
        let t = self.blk_id(ind)?;
        Ok(self.env.app(t, &[]))
    }

    pub fn lean_name<'t>(&self, tc: &TypeChecker<'_, 't, '_>, n: NamePtr<'t>) -> String {
        match tc.ctx.read_name(n) {
            Name::Anon => String::new(),
            Name::Str(pfx, s, _) => {
                let p = self.lean_name(tc, pfx);
                let s = tc.ctx.read_string(s).to_string();
                if p.is_empty() { s } else { format!("{p}.{s}") }
            }
            Name::Num(pfx, k, _) => {
                let p = self.lean_name(tc, pfx);
                if p.is_empty() { k.to_string() } else { format!("{p}.{k}") }
            }
        }
    }

    /// Reserve the level-variable names of every declaration, so constants never take them.
    fn reserve_level_names(&mut self, export: &ExportFile<'_>) {
        for d in export.declars.values() {
            export.with_ctx(|ctx| {
                for &l in ctx.read_levels(d.info().uparams).iter() {
                    if let Level::Param(n, _) = ctx.read_level(l) {
                        if let Name::Str(_, s, _) = ctx.read_name(n) {
                            let m = mangle(ctx.read_string(s));
                            if !self.terms.contains(&m) {
                                self.terms.reserve(&m);
                            }
                            self.var_names.reserve(&m);
                        }
                    }
                }
            });
        }
    }

    /// The `.mm0` text of the generated statements; in part mode only those of the
    /// declarations not replayed (the earlier parts state the others).
    pub fn generated_text(&self) -> String {
        let from = if self.parts { self.own_from.unwrap_or(self.spec_len) } else { self.spec_len };
        let mut out = String::new();
        for &st in &self.env.order[from.max(self.spec_len)..] {
            if let Some(t) = self.env.stmt_text(st) {
                out.push('\n');
                out.push_str(&t);
            }
        }
        out
    }

    pub fn num_generated(&self) -> usize { self.env.order.len() - self.spec_len }

    /// Generate certificates for every declaration of the export, in order. Stops at the first
    /// declaration that cannot be certified, unless `keep_going` (then it is skipped, and so is
    /// everything that depends on it).
    ///
    /// Each declaration's statements are written to `out` as soon as it is done, and its proofs
    /// and unused expressions are then freed.
    pub fn run(&mut self, export: &ExportFile<'_>, keep_going: bool, out: &mut mm0kit::mmb::Writer) -> R<()> {
        self.reserve_level_names(export);
        // the operations with defining equations in the spec (`natlit::eq_ops`): each is
        // declared in a type checker extended by itself, so that its equations can be derived
        let eq_names: Vec<NamePtr<'_>> = natlit::eq_ops().filter_map(|n| export.find_name(n)).collect();
        let progress = std::env::var_os("LEAN0_PROGRESS").is_some();
        // with progress lines, also report a declaration still running after each minute
        let current: std::sync::Arc<std::sync::Mutex<Option<(String, Instant)>>> = Default::default();
        if progress {
            let current = current.clone();
            std::thread::spawn(move || loop {
                std::thread::sleep(std::time::Duration::from_secs(60));
                if let Some((name, t)) = &*current.lock().unwrap() {
                    let secs = t.elapsed().as_secs();
                    if secs >= 60 {
                        eprintln!("still running: {name} ({secs} s)");
                    }
                }
            });
        }
        for (i, d) in export.declars.values().enumerate() {
            if self.shard.is_some_and(|(_, hi)| i >= hi) {
                break
            }
            self.replay = self.shard.is_some_and(|(lo, _)| i < lo);
            if !self.replay && self.own_from.is_none() {
                out.flush(&self.env).map_err(|e| format!("writing the certificate: {e}"))?;
                self.own_from = Some(self.env.order.len());
                self.replayed_bytes = out.written();
            }
            let start = Instant::now();
            let nodes0 = self.env.num_pfs();
            let exprs0 = self.env.num_nodes();
            let order0 = self.env.order.len();
            if progress && !self.replay {
                let name = export.with_tc_and_declar(*d.info(), |tc| self.lean_name(tc, d.info().name));
                *current.lock().unwrap() = Some((name, start));
            }
            self.cost_enter("gen.declar");
            let all = &export.declars;
            let (name, r) = match nested_block(d, all) {
                // a declaration of a nested block: its type checker sees the kernel's auxiliary
                // types (and, at the block's head, the block's own types)
                Some(id) => export.with_ctx(|ctx| {
                    let info = *d.info();
                    let at_head = matches!(d, Declar::Inductive(_));
                    let (name, nst) = ctx.with_tc(EnvLimit::ByName(info.name), |tc| (self.lean_name(tc, info.name), build_nested(tc, &id, all, at_head)));
                    let r = nst.and_then(|nst| ctx.with_tc_and_declar_ext(info, &nst.ext, |tc| self.declar(tc, d, all, Some(&nst))));
                    (name, r)
                }),
                None if matches!(d, Declar::Definition { .. }) && eq_names.contains(&d.info().name) => export.with_ctx(|ctx| {
                    let info = *d.info();
                    let mut ext = DeclarMap::default();
                    ext.insert(info.name, d.clone());
                    ctx.with_tc_and_declar_ext(info, &ext, |tc| (self.lean_name(tc, info.name), self.declar(tc, d, all, None)))
                }),
                None => export.with_tc_and_declar(*d.info(), |tc| (self.lean_name(tc, d.info().name), self.declar(tc, d, all, None))),
            };
            self.cost_exit();
            if progress {
                *current.lock().unwrap() = None;
            }
            let (ok, message, mism) = match &r {
                Ok(m) => (true, String::new(), *m),
                Err(e) => (false, e.clone(), 0),
            };
            let kind = match d {
                Declar::Axiom { .. } => "axiom",
                Declar::Definition { .. } => "def",
                Declar::Theorem { .. } => "theorem",
                Declar::Opaque { .. } => "opaque",
                Declar::Quot { .. } => "quot",
                Declar::Inductive(..) => "inductive",
                Declar::Constructor(..) => "constructor",
                Declar::Recursor(..) => "recursor",
            };
            if !self.replay {
                self.stats.push(DeclStat {
                    name: name.clone(),
                    kind,
                    ok,
                    message,
                    proof_nodes: self.env.num_pfs() - nodes0,
                    type_mismatches: mism,
                    micros: start.elapsed().as_micros(),
                });
            }
            if progress && !self.replay {
                let st = self.stats.last().unwrap();
                let rss = memory_mb("VmRSS").map(|m| m.to_string()).unwrap_or_default();
                eprintln!("{}\t{}\t{}\t{}\t{}\t{}\t{}", st.name, st.ok, st.proof_nodes, st.micros / 1000, rss, self.env.num_nodes(), heap_in_use_mb());
            }
            out.decl = i as u32;
            out.owned = !self.replay;
            out.flush(&self.env).map_err(|e| format!("writing the certificate: {e}"))?;
            if progress && !self.replay && self.stats.len() % 1000 == 0 {
                let mut parts = self.env.mem_report();
                parts.push(("gen thm names", self.thms.approx_bytes()));
                parts.push(("gen term names", self.terms.approx_bytes()));
                parts.push(("writer", out.approx_bytes()));
                let line: Vec<String> = parts.iter().map(|(k, b)| format!("{k} {}", b >> 20)).collect();
                eprintln!("mem: {} decls, in use {} MB: {}", self.stats.len(), heap_in_use_mb(), line.join(", "));
            }
            self.forget_declaration(nodes0, exprs0, order0);
            if !ok {
                // Statements of a partly generated declaration cannot be taken back, except local
                // lemmas (valid theorems, if unused).
                let emitted = self.env.order[order0..].iter().any(|s| !matches!(s, Stmt::Thm(t) if self.env.thms[t.0 as usize].local));
                if emitted {
                    return Err(format!("{name}: failed after emitting statements: {}", r.unwrap_err()))
                }
                if !keep_going {
                    return Err(format!("{name}: {}", r.unwrap_err()))
                }
            }
        }
        if self.stage_b > 0 {
            eprintln!("lean0: {} inductive blocks certified by the schema, {} level-congruence axioms for opaque constants in block data",
                self.stage_b, self.eeqv_axioms.len());
        }
        if self.lit_stage_b + self.lit_stage_a.len() > 0 {
            eprintln!("lean0: {} literal operations certified by their defining equations, {} with generated axioms", self.lit_stage_b, self.lit_stage_a.len());
            for (n, why) in &self.lit_stage_a {
                eprintln!("  stage A: {n}: {why}");
            }
        }
        Ok(())
    }

    /// Take back the statements and proofs a block's stage-B attempt made (none written yet),
    /// and what it registered under the block's type names.
    pub fn rollback(&mut self, order0: usize, pfs0: usize, names: &[String]) {
        self.env.rollback(order0);
        self.env.truncate_pfs(pfs0);
        let nthms = self.env.thms.len();
        self.eeqv_axioms.retain(|_, th| (th.0 as usize) < nthms);
        self.nat_eqs.retain(|_, th| (th.0 as usize) < nthms);
        self.bins.forget_pfs(pfs0);
        self.lean.reset();
        self.lv.reset();
        for n in names {
            self.consts.remove(n);
            self.blocks.remove(n);
            self.blks.remove(n);
        }
    }

    /// Free what the declaration that started at proof node `pfs0`, expression node `exprs0` and
    /// statement `order0` made, except its statements (which must have been written out).
    fn forget_declaration(&mut self, pfs0: usize, exprs0: usize, order0: usize) {
        self.env.forget_proofs(order0);
        self.env.forget_local_names(order0);
        self.env.truncate_pfs(pfs0);
        self.bins.forget_pfs(pfs0);
        self.lv.reset();
        let mut roots = self.lean.nats().to_vec();
        for si in self.structs.values() {
            roots.push(si.sort);
            roots.extend(&si.field_tys);
        }
        let map = self.env.compact_nodes(exprs0, order0, &roots);
        self.lean.remap_nodes(exprs0, &map);
        self.bins.forget_nodes(exprs0);
        let f = |e: &mut E| {
            if let Some(&e2) = map.get(e) {
                *e = e2
            }
        };
        for si in self.structs.values_mut() {
            f(&mut si.sort);
            si.field_tys.iter_mut().for_each(f);
        }
    }

    /// Open the cost centre `name` (`LEAN0_COSTS`); `cost_exit` closes it.
    pub fn cost_enter(&mut self, name: &'static str) {
        if let Some(c) = &mut self.costs {
            self.env.cur_tag = c.enter(name, self.env.num_pfs());
        }
    }

    pub fn cost_exit(&mut self) {
        if let Some(c) = &mut self.costs {
            self.env.cur_tag = c.exit(self.env.num_pfs());
        }
    }

    fn level_args<'t>(&mut self, tc: &TypeChecker<'_, 't, '_>, uparams: &[NamePtr<'t>]) -> Vec<String> {
        let mut seen = Names::default();
        uparams
            .iter()
            .map(|&n| {
                let base = match tc.ctx.read_name(n) {
                    Name::Str(_, s, _) => mangle(tc.ctx.read_string(s)),
                    _ => "u".to_string(),
                };
                // constants avoid level names (see `reserve_level_names`), but spec terms do not
                let base = if self.env.has_term(&base) { format!("u_{base}") } else { base };
                seen.fresh(&base)
            })
            .collect()
    }

    fn declar<'t>(&mut self, tc: &mut TypeChecker<'_, 't, '_>, d: &Declar<'t>, all: &DeclarMap<'t>, nested: Option<&Nested<'t>>) -> R<usize> {
        let info = *d.info();
        let uparams: Vec<NamePtr<'t>> = tc
            .ctx
            .read_levels(info.uparams)
            .iter()
            .map(|&l| match tc.ctx.read_level(l) {
                Level::Param(n, _) => n,
                _ => panic!("universe parameter list with a non-parameter"),
            })
            .collect();
        let lean_name = self.lean_name(tc, info.name);
        let lvl_names = self.level_args(tc, &uparams);
        let cname = match self.predeclared.get(&lean_name) {
            Some(c) => c.clone(),
            None => self.terms.fresh(&mangle(&lean_name)),
        };
        self.lean.reset();
        self.lv.reset();
        let lemma_args = self.g_args(&lvl_names);
        let sig = Sig { lean_name, cname, lvl_names };
        let mut el = Elab::new(tc, self, uparams, sig.cname.clone(), lemma_args);
        match d {
            Declar::Axiom { .. } => {
                opaque(&mut el, &sig, info.ty, "axiom")?;
            }
            Declar::Inductive(id) => {
                if id.all_ind_names.first() == Some(&id.info.name) {
                    let (order0, pfs0) = (el.g.env.order.len(), el.g.env.num_pfs());
                    // a block the schema does not certify is an error: no generated axioms
                    if let Err(e) = crate::induct::block_head(&mut el, &sig, id, all, nested) {
                        let names: Vec<String> = id.all_ind_names.iter().map(|&n| el.g.lean_name(el.tc, n)).collect();
                        el.g.rollback(order0, pfs0, &names);
                        el.forget_proofs();
                        return Err(format!("the inductive block is not certified: {e}"))
                    }
                } else if !el.g.blocks.contains_key(&sig.lean_name) {
                    // a later type of a block: its lemmas were made with the block
                    return Err("its inductive block is not certified".into())
                }
                return Ok(el.type_mismatches)
            }
            Declar::Constructor(cd) => {
                if crate::induct::constructor(&mut el, &sig, cd, all, nested)? {
                    if sig.lean_name == "Nat.zero" || sig.lean_name == "Nat.succ" {
                        natlit::lit_axioms(&mut el, &sig.lean_name, info.ty)?;
                    }
                    return Ok(el.type_mismatches)
                }
                return Err("its inductive block is not certified".into())
            }
            Declar::Recursor(rd) => {
                if crate::induct::recursor(&mut el, &sig, rd, all, nested)? {
                    return Ok(el.type_mismatches)
                }
                return Err("its inductive block is not certified".into())
            }
            Declar::Quot { .. } => quot_spec(&mut el, &sig, info.ty)?,
            Declar::Opaque { val, .. } => {
                let pv = if el.g.replay {
                    None
                } else {
                    let (vt, pv) = el.infer(*val)?;
                    Some(el.cast(pv, vt, info.ty)?)
                };
                let (v, t) = (el.tr(*val)?, el.tr(info.ty)?);
                opaque(&mut el, &sig, info.ty, "opaque constant")?;
                let g = &mut *el.g;
                let gv = g.env.var(0);
                let concl = g.env.app_n("ty", &[gv, v, t]);
                let p = pv.map(|pv| g.env.convert(pv, concl)).transpose().map_err(|e| e.0)?;
                let name = g.thms.fresh(&format!("{}_val", sig.cname));
                let args = g.g_args(&sig.lvl_names);
                add_thm(&mut g.env, &name, args, vec![], concl, false, false, p, &format!("The value of `{}` has its type.", sig.lean_name))?;
            }
            Declar::Definition { val, .. } | Declar::Theorem { val, .. } => {
                let public_body = matches!(d, Declar::Definition { .. });
                let pv = if el.g.replay {
                    None
                } else {
                    let (vt, pv) = el.infer(*val)?;
                    Some(el.cast(pv, vt, info.ty)?)
                };
                // a theorem of an earlier part: its proof term is opaque here (see `parts`)
                let opaque_proof = el.g.replay && el.g.parts && !public_body;
                let body = if opaque_proof { None } else { Some(el.tr(*val)?) };
                let t = el.tr(info.ty)?;
                let g = &mut *el.g;
                let n = sig.lvl_names.len();
                // the def body takes the levels as its only arguments: shift Var(i+1) to Var(i)
                let mut shift = vec![g.env.var(0)];
                shift.extend((0..n).map(|i| g.env.var(i as u16)));
                let kind = match body {
                    Some(b) => TermKind::Def { body: g.env.subst(b, &shift), public_body },
                    None => TermKind::Term,
                };
                let doc = if public_body {
                    format!("Lean definition `{}`.", sig.lean_name)
                } else {
                    format!("Lean theorem `{}`. Its proof term is given in the .mmb.", sig.lean_name)
                };
                let lvl_args = g.lvl_args(&sig.lvl_names);
                let expr_s = g.env.sort_names["expr"];
                let term = add_term(&mut g.env, &sig.cname, lvl_args, expr_s, kind, &doc)?;
                let gv = g.env.var(0);
                let us: Vec<E> = (0..n).map(|i| g.env.var(1 + i as u16)).collect();
                let c = g.env.app(term, &us);
                let concl = g.env.app_n("ty", &[gv, c, t]);
                let p = pv.map(|pv| g.env.convert(pv, concl)).transpose().map_err(|e| e.0)?;
                let ty_name = g.thms.fresh(&format!("{}_ty", sig.cname));
                let args = g.g_args(&sig.lvl_names);
                g.cost_enter("gen.split");
                let ty = add_thm(&mut g.env, &ty_name, args, vec![], concl, false, false, p, &format!("`{}` has its declared type.", sig.lean_name));
                g.cost_exit();
                let ty = ty?;
                // theorem c_closed (k) (us): closed k (c us), from the body (public, so that a later
                // part can restate it)
                g.lean.reset();
                let kv = g.env.var(0);
                let cl_concl = g.env.app_n("closed", &[kv, c]);
                let pc = if g.replay {
                    None
                } else {
                    g.cost_enter("gen.closed");
                    let pc = g.lean.closed(&mut g.env, kv, body.unwrap()).map_err(|e| e.0);
                    g.cost_exit();
                    Some(g.env.convert(pc?, cl_concl).map_err(|e| e.0)?)
                };
                let cl_args = g.k_args(&sig.lvl_names);
                let cl_name = g.thms.fresh(&format!("{}_closed", sig.cname));
                let cl = add_thm(&mut g.env, &cl_name, cl_args, vec![], cl_concl, false, false, pc, &format!("`{}` has no loose bound variables.", sig.lean_name))?;
                g.lean.const_closed.insert(term, cl);
                g.consts.insert(sig.lean_name.clone(), ConstInfo { term, kind: ConstKind::Def, nlevels: n, ty_thm: ty });
                natlit::op_axioms(&mut el, &sig.lean_name, &sig.cname, info.ty)?;
            }
        }
        Ok(el.type_mismatches)
    }

    pub(crate) fn lvl_args(&self, lvl_names: &[String]) -> Vec<(String, u8)> {
        let lvl_s = self.env.sort_names["lvl"];
        lvl_names.iter().map(|s| (s.clone(), lvl_s)).collect()
    }

    /// `(G: ctx)` followed by the level arguments.
    pub(crate) fn g_args(&self, lvl_names: &[String]) -> Vec<(String, u8)> {
        let mut v = vec![("G".to_string(), self.env.sort_names["ctx"])];
        v.extend(self.lvl_args(lvl_names));
        v
    }

    /// `(k: nat)` followed by the level arguments.
    pub(crate) fn k_args(&self, lvl_names: &[String]) -> Vec<(String, u8)> {
        let mut v = vec![("k".to_string(), self.env.sort_names["nat"])];
        v.extend(self.lvl_args(lvl_names));
        v
    }

    /// A name for the primed copy of level variable `s`.
    pub(crate) fn var_names_fresh2(&mut self, s: &str, taken: &[String]) -> String {
        let mut c = format!("{s}2");
        let mut i = 3;
        while taken.contains(&c) || self.env.has_term(&c) {
            c = format!("{s}{i}");
            i += 1;
        }
        c
    }
}

/// A memory figure of this process in MB (`VmRSS`: resident now, `VmHWM`: peak), where
/// `/proc` has it (Linux).
/// Bytes the allocator has handed out and not taken back (glibc), in MB: resident memory
/// beyond it is fragmentation or freed memory not yet returned.
pub fn heap_in_use_mb() -> u64 {
    #[repr(C)]
    struct MallInfo2 {
        arena: usize,
        ordblks: usize,
        smblks: usize,
        hblks: usize,
        hblkhd: usize,
        usmblks: usize,
        fsmblks: usize,
        uordblks: usize,
        fordblks: usize,
        keepcost: usize,
    }
    extern "C" {
        fn mallinfo2() -> MallInfo2;
    }
    let m = unsafe { mallinfo2() };
    ((m.uordblks + m.hblkhd) >> 20) as u64
}

pub fn memory_mb(field: &str) -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    let v = s.lines().find_map(|l| l.strip_prefix(field)?.strip_prefix(':'))?;
    let kb: u64 = v.trim().strip_suffix("kB")?.trim().parse().ok()?;
    Some(kb / 1024)
}

/// The names of the declaration being generated.
pub(crate) struct Sig {
    pub lean_name: String,
    pub cname: String,
    pub lvl_names: Vec<String>,
}

/// Variables of a generated statement: names that are not term names, and their indices.
pub(super) struct Vars {
    pub(super) args: Vec<(String, u8)>,
}

impl Vars {
    pub(crate) fn new() -> Self { Vars { args: Vec::new() } }

    pub(super) fn add(&mut self, env: &mut Env, base: &str, sort: &str) -> E {
        let mut name = base.to_string();
        while env.has_term(&name) || self.args.iter().any(|a| a.0 == name) {
            name.push('_');
        }
        let s = env.sort_names[sort];
        self.args.push((name, s));
        env.var(u16::try_from(self.args.len() - 1).unwrap())
    }

    pub(crate) fn many(&mut self, env: &mut Env, base: &str, sort: &str, n: usize) -> Vec<E> {
        (0..n).map(|i| self.add(env, &format!("{base}{}", i + 1), sort)).collect()
    }

    pub(crate) fn lvls(&mut self, env: &mut Env, names: &[String], suffix: &str) -> Vec<E> {
        names.iter().map(|n| self.add(env, &format!("{n}{suffix}"), "lvl")).collect()
    }
}

pub(crate) fn apps(g: &mut Gen, f: E, args: &[E]) -> E {
    args.iter().fold(f, |f, &a| g.lean.app(&mut g.env, f, a))
}

/// An opaque constant: its own atom (`term c_atom: atom`) and the public definition
/// `def c (us): expr = $ cst c_atom (lcons u1 ... lnil) $` (audit §10), with its
/// well-formedness and closedness theorems and its `constDF` axiom. Used for Lean axioms
/// and opaque definitions.
fn opaque<'t>(el: &mut Elab<'_, '_, 't, '_>, sig: &Sig, ty: nanoda_lib::util::ExprPtr<'t>, what: &str) -> R<TId> {
    let (st, pt) = el.infer(ty)?;
    let (level, pt) = el.as_sort(pt, st)?;
    let t = el.tr(ty)?;
    let u = el.trl(level)?;
    let g = &mut *el.g;
    let n = sig.lvl_names.len();
    let lean_name = &sig.lean_name;
    let expr_s = g.env.sort_names["expr"];
    let lvl_args = g.lvl_args(&sig.lvl_names);
    let atom_s = g.env.sort_names["atom"];
    let atom_name = g.terms.fresh(&format!("{}_atom", sig.cname));
    let atom = add_term(&mut g.env, &atom_name, vec![], atom_s, TermKind::Term, &format!("The atom of Lean {what} `{lean_name}`."))?;
    let atom = g.env.app(atom, &[]);
    // the level list at the given levels
    let lvl_list = |g: &mut Gen, us: &[E]| {
        let mut ls = g.env.app_n("lnil", &[]);
        for &l in us.iter().rev() {
            ls = g.env.app_n("lcons", &[l, ls]);
        }
        ls
    };
    let body_lvls: Vec<E> = (0..n).map(|i| g.env.var(i as u16)).collect();
    let ls = lvl_list(g, &body_lvls);
    let body = g.env.app_n("cst", &[atom, ls]);
    let term = add_term(&mut g.env, &sig.cname, lvl_args, expr_s, TermKind::Def { body, public_body: true }, &format!("Lean {what} `{lean_name}`."))?;
    // theorem c_wf (G) (us): ty G T (srt u)
    let gv = g.env.var(0);
    let su = g.lean.srt(&mut g.env, u);
    let wf_concl = g.env.app_n("ty", &[gv, t, su]);
    let p = g.env.convert(pt, wf_concl).map_err(|e| e.0)?;
    let wf_name = g.thms.fresh(&format!("{}_wf", sig.cname));
    let args = g.g_args(&sig.lvl_names);
    add_thm(&mut g.env, &wf_name, args, vec![], wf_concl, false, false, Some(p), &format!("The type of `{lean_name}` is a type."))?;
    // axiom c_df (G) (us us2): leqv us us2 > deq G (c us) (c us2) T
    let mut df_args = g.g_args(&sig.lvl_names);
    let lvl_s = g.env.sort_names["lvl"];
    for s in &sig.lvl_names {
        let s2 = g.var_names_fresh2(s, &sig.lvl_names);
        df_args.push((s2, lvl_s));
    }
    let us: Vec<E> = (0..n).map(|i| g.env.var(1 + i as u16)).collect();
    let us2: Vec<E> = (0..n).map(|i| g.env.var(1 + (n + i) as u16)).collect();
    let hyps: Vec<E> = us.iter().zip(&us2).map(|(&a, &b)| g.env.app_n("leqv", &[a, b])).collect();
    let c1 = g.env.app(term, &us);
    let c2 = g.env.app(term, &us2);
    let df_concl = g.lean.deq(&mut g.env, gv, c1, c2, t);
    let df_name = g.thms.fresh(&format!("{}_df", sig.cname));
    let df = add_thm(&mut g.env, &df_name, df_args, hyps, df_concl, true, false, None, &format!("`{lean_name}` has its type, at any equivalent levels (`constDF`)."))?;
    // theorem c_closed (k: nat) (us): closed k (c us), by `closed_cst`
    let kv = g.env.var(0);
    let cl_concl = g.env.app_n("closed", &[kv, c1]);
    let cl_args = g.k_args(&sig.lvl_names);
    let cl_name = g.thms.fresh(&format!("{}_closed", sig.cname));
    let pc = if g.replay {
        None
    } else {
        let ls = lvl_list(g, &us);
        let p = g.env.thm_n("closed_cst", &[kv, atom, ls], &[]).map_err(|e| e.0)?;
        Some(g.env.convert(p, cl_concl).map_err(|e| e.0)?)
    };
    let cl = add_thm(&mut g.env, &cl_name, cl_args, vec![], cl_concl, false, false, pc, &format!("`{lean_name}` has no loose bound variables."))?;
    g.lean.const_closed.insert(term, cl);
    g.consts.insert(lean_name.clone(), ConstInfo { term, kind: ConstKind::Opaque, nlevels: n, ty_thm: df });
    Ok(term)
}

/// A quotient primitive as the spec's constant (`quot`, `quot_mk`, `quot_lift`, `quot_ind`,
/// typed by `quot_ty` and so on, reducing by `quot_lift_mk`/`quot_ind_mk`; audit §4), when
/// the export's type is the spec's: `theorem Quot_df` (`constDF`, from `eeqv_df`), and for
/// `Quot.lift` and `Quot.ind` the reduction lemma `Quot_lift_mk`, `Quot_ind_mk`. An error
/// when the type differs: no axioms are generated for a quotient primitive.
fn quot_spec<'t>(el: &mut Elab<'_, '_, 't, '_>, sig: &Sig, ty: nanoda_lib::util::ExprPtr<'t>) -> R<()> {
    let (term, ty_ax, eqv_ax, red) = match sig.lean_name.as_str() {
        "Quot" => ("quot", "quot_ty", "eeqv_quot", None),
        "Quot.mk" => ("quot_mk", "quot_mk_ty", "eeqv_quot_mk", None),
        "Quot.lift" => ("quot_lift", "quot_lift_ty", "eeqv_quot_lift", Some("quot_lift_mk")),
        "Quot.ind" => ("quot_ind", "quot_ind_ty", "eeqv_quot_ind", Some("quot_ind_mk")),
        n => return Err(format!("unknown quotient primitive {n}")),
    };
    if !el.g.env.has_term(term) || !el.g.env.has_thm(ty_ax) {
        return Err("the spec has no such quotient primitive".into())
    }
    let t = el.tr(ty)?;
    let g = &mut *el.g;
    let term = g.env.term_id(term);
    let n = g.env.terms[term.0 as usize].args.len();
    if n != sig.lvl_names.len() {
        return Err("the quotient primitive's universe parameters are not the spec's".into())
    }
    let gv = g.env.var(0);
    let us: Vec<E> = (0..n).map(|i| g.env.var(1 + i as u16)).collect();
    let us2: Vec<E> = (0..n).map(|i| g.env.var(1 + (n + i) as u16)).collect();
    // the spec's typing axiom at `G, us`: `ty G (c us) T`
    let ty_th = g.env.thm_id(ty_ax);
    let concl = g.env.plain_concl(ty_th);
    let args: Vec<E> = std::iter::once(gv).chain(us.iter().copied()).collect();
    let stmt = g.env.subst(concl, &args);
    let Some((_, [_, c1, spec_t])) = g.env.head(stmt) else { return Err(format!("{ty_ax}: not a typing")) };
    let (c1, spec_t) = (*c1, *spec_t);
    if spec_t != t {
        return Err("the quotient primitive's type is not the spec's".into())
    }
    let c2 = g.env.app(term, &us2);
    let hyps: Vec<E> = us.iter().zip(&us2).map(|(&a, &b)| g.env.app_n("leqv", &[a, b])).collect();
    let concl = g.lean.deq(&mut g.env, gv, c1, c2, t);
    let mut df_args = g.g_args(&sig.lvl_names);
    let lvl_s = g.env.sort_names["lvl"];
    for s in &sig.lvl_names {
        let s2 = g.var_names_fresh2(s, &sig.lvl_names);
        df_args.push((s2, lvl_s));
    }
    let proof = if g.replay {
        None
    } else {
        let p_ty = g.env.thm(ty_th, &args, &[]).map_err(|e| e.0)?;
        let hs: Vec<mm0kit::env::P> = hyps.iter().enumerate().map(|(i, &h)| g.env.hyp(i as u16, h)).collect();
        let eqv_args: Vec<E> = us.iter().chain(&us2).copied().collect();
        let p_eq = g.env.thm_n(eqv_ax, &eqv_args, &hs).map_err(|e| e.0)?;
        Some(g.env.thm_n("eeqv_df", &[gv, c1, c2, t], &[p_ty, p_eq]).map_err(|e| e.0)?)
    };
    let spec_name = g.env.terms[term.0 as usize].name.clone();
    let df_name = g.thms.fresh(&format!("{}_df", sig.cname));
    let df = add_thm(&mut g.env, &df_name, df_args, hyps, concl, false, false, proof,
        &format!("`{}` (the spec's `{spec_name}`) has its type, at any equivalent levels (`constDF`).", sig.lean_name))?;
    g.consts.insert(sig.lean_name.clone(), ConstInfo { term, kind: ConstKind::Opaque, nlevels: n, ty_thm: df });
    if let Some(r) = red {
        // the spec's closed equation over any base context
        let name = g.thms.fresh(&format!("{}_mk", sig.cname));
        let args = g.g_args(&sig.lvl_names);
        let th = crate::induct::closed_over_base(g, r, &us, &name, args, &format!("Reduction of `{}` on `Quot.mk` (the spec's `{r}`, over any base context).", sig.lean_name))?;
        g.quot_red.insert(sig.lean_name.clone(), th);
    }
    Ok(())
}

/// What the structure lemmas (`induct::structure`) need from the constructor's type: each field's type (a de Bruijn
/// term under the parameters and earlier fields), whether it is a proposition, the level of
/// its sort, and the structure's sort level.
pub(crate) struct Fields {
    pub tys: Vec<E>,
    pub is_prop: Vec<bool>,
    pub levels: Vec<E>,
    pub sort: E,
}

pub(crate) fn structure_fields<'t>(el: &mut Elab<'_, '_, 't, '_>, ind: NamePtr<'t>, ctor_ty: nanoda_lib::util::ExprPtr<'t>) -> R<Fields> {
    let ind_data = el.tc.env.get_structure(&ind, true).cloned().unwrap();
    let np = ind_data.num_params as usize;
    // field types (as de Bruijn terms under the parameters and earlier fields), and which are props
    let mut field_tys = Vec::new();
    let mut is_prop = Vec::new();
    let mut levels = Vec::new();
    let mut ty = ctor_ty;
    let mut opened = 0;
    let res = (|| {
        while let Expr::Pi { binder_name, binder_style, binder_type, body, .. } = el.tc.ctx.read_expr(ty) {
            let d = el.depth();
            if opened >= np {
                field_tys.push(el.tr_at(binder_type, d)?);
            }
            // binder types refer to earlier binders by Var; open them in order
            let bt = el.inst_locals(binder_type);
            if opened >= np {
                let s = el.tc.infer(bt, nanoda_lib::tc::InferFlag::InferOnly);
                let s = el.tc.whnf(s);
                let Expr::Sort { level, .. } = el.tc.ctx.read_expr(s) else { return Err("field type is not a type".to_string()) };
                is_prop.push(el.tc.ctx.is_zero(level));
                levels.push(el.trl(level)?);
            }
            el.open_pub(binder_name, binder_style, bt)?;
            opened += 1;
            ty = body;
        }
        Ok(())
    })();
    for _ in 0..opened {
        el.close_pub();
    }
    res?;
    // the structure's sort
    let mut sty = ind_data.info.ty;
    for _ in 0..np {
        let Expr::Pi { body, .. } = el.tc.ctx.read_expr(sty) else { return Err("structure type".into()) };
        sty = body;
    }
    let Expr::Sort { level, .. } = el.tc.ctx.read_expr(sty) else { return Err("structure type is not a sort".into()) };
    let sort = el.trl(level)?;
    Ok(Fields { tys: field_tys, is_prop, levels, sort })
}

/// The level `l` may be zero: it is not provably at least 1 (`lmax 1 l ≈ l` fails).
pub(crate) fn level_may_be_zero(g: &mut Gen, l: E) -> bool {
    let z = g.env.app_n("lz", &[]);
    let one = g.env.app_n("ls", &[z]);
    let m = g.env.app_n("lmax", &[one, l]);
    g.lv.equiv(&g.lean, &mut g.env, m, l).is_err()
}

/// The `inst` hypotheses that give the type of the projection `proj b i e` of `e : S ps`:
/// the field's type `fty` (under the parameters and the `i` earlier fields, over the level
/// variables `1..`, instantiated by `subst`) with the parameters and then the earlier
/// projections of `e` put in, outermost first (the spec's `pinst`/`qinst`: a simultaneous
/// substitution), each result a fresh variable `R`. Returns the hypotheses and the last
/// result.
pub(crate) fn field_inst_hyps(g: &mut Gen, v: &mut Vars, fty: E, subst: &[E], ps: &[E], i: usize, blk: E, e: E) -> (Vec<E>, E) {
    let np = ps.len();
    let n = np + i;
    let mut cur = g.env.subst(fty, subst);
    let mut hyps = Vec::new();
    for j in 0..n {
        let a = if j < np { ps[j] } else { g.lean.proj(&mut g.env, blk, j - np, e) };
        let k = g.lean.nat(&mut g.env, n - 1 - j);
        let r = v.add(&mut g.env, "R", "expr");
        hyps.push(g.env.app_n("inst", &[k, cur, a, r]));
        cur = r;
    }
    (hyps, cur)
}

pub(crate) fn add_term(env: &mut Env, name: &str, args: Vec<(String, u8)>, ret: u8, kind: TermKind, doc: &str) -> R<TId> {
    env.add_term(TermDecl { name: name.into(), args, ret, kind, local: false, doc: Some(doc.into()) }).map_err(|e| e.0)
}

pub(crate) fn add_thm(
    env: &mut Env, name: &str, args: Vec<(String, u8)>, hyps: Vec<E>, concl: E, axiom: bool, local: bool,
    proof: Option<mm0kit::env::P>, doc: &str,
) -> R<ThId> {
    let doc = if doc.is_empty() { None } else { Some(doc.into()) };
    env.add_thm_split(ThmDecl { name: name.into(), args: args.into(), hyps: hyps.into(), concl, axiom, local, proof, doc }, split_budget()).map_err(|e| e.0)
}

/// A nested block as the kernel checks it (`ElimNestedInductive`; audit §4): the declared
/// types with the nested occurrences in their constructors replaced by auxiliary types, then
/// the auxiliary types (`InductiveCheckState`), and the auxiliary types as temporary
/// declarations for the type checker of each of the block's declarations.
pub struct Nested<'t> {
    pub st: InductiveCheckState<'t>,
    pub ext: DeclarMap<'t>,
}

/// The first type of the nested block `d` belongs to (a type, constructor or recursor of one).
fn nested_block<'t>(d: &Declar<'t>, all: &DeclarMap<'t>) -> Option<InductiveData<'t>> {
    let first = match d {
        Declar::Inductive(id) => *id.all_ind_names.first()?,
        Declar::Constructor(cd) => match all.get(&cd.inductive_name)? {
            Declar::Inductive(id) => *id.all_ind_names.first()?,
            _ => return None,
        },
        Declar::Recursor(rd) => *rd.all_inductives.first()?,
        _ => return None,
    };
    match all.get(&first)? {
        Declar::Inductive(id) if id.is_nested => Some(id.clone()),
        _ => None,
    }
}

/// The kernel's specialization of the nested block `id` (nanoda's `specialize_nested`, the
/// export's own declarations as its input) and the temporary declarations: the auxiliary
/// types, and at the block's head the declared types too (so that the constructors' fields
/// can be typed there).
fn build_nested<'t>(tc: &mut TypeChecker<'_, 't, '_>, id: &InductiveData<'t>, all: &DeclarMap<'t>, at_head: bool) -> R<Nested<'t>> {
    let mut headers = Vec::new();
    let mut ext = DeclarMap::default();
    for &n in id.all_ind_names.iter() {
        let Some(Declar::Inductive(d)) = all.get(&n) else { return Err("a type of the block is missing from the export".into()) };
        let mut ctors = Vec::new();
        for &c in d.all_ctor_names.iter() {
            let Some(Declar::Constructor(cd)) = all.get(&c) else { return Err("a constructor of the block is missing from the export".into()) };
            ctors.push(CtorHeader { name: c, ty: cd.info.ty });
        }
        headers.push(IndTyHeader { name: n, ty: d.info.ty, ctors });
        if at_head {
            ext.insert(n, Declar::Inductive(d.clone()));
        }
    }
    let st = tc.specialize_nested(id, headers);
    let all_names: std::sync::Arc<[NamePtr<'t>]> = st.all_inductives_incl_specialized.iter().map(|h| h.name).collect();
    for h in st.all_inductives_incl_specialized.iter().skip(id.all_ind_names.len()) {
        let binders = tc.ctx.pi_telescope_size(h.ty);
        // only `info` is read for them (inferring the type of the constant)
        let d = InductiveData {
            info: DeclarInfo { name: h.name, ty: h.ty, uparams: st.uparams },
            is_recursive: true,
            is_nested: true,
            num_params: id.num_params,
            num_indices: binders.saturating_sub(id.num_params),
            all_ind_names: all_names.clone(),
            all_ctor_names: h.ctors.iter().map(|c| c.name).collect(),
        };
        ext.insert(h.name, Declar::Inductive(d));
    }
    Ok(Nested { st, ext })
}
