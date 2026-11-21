//! The spec's relations as functions: a mechanical check that each relation of
//! `spec/lean.mm0` other than the judgment's rules is the definition it is read as.
//!
//! Every relation has a declared *kind* and *mode* ([`TABLE`]): a *computing* relation is
//! the graph of a function from its input positions (`+`) to its output positions (`-`), a
//! *checking* relation a predicate on its inputs, and a *search* relation one whose clauses
//! are tried in order and may overlap (`rst`). The check establishes, per clause, that the
//! clause is *well-moded* (the inputs of every computing premise, and the outputs of the
//! clause, are determined by the clause's inputs through the premises: so the clause reads
//! as a defining equation, with the checking premises as side conditions), and, per
//! computing relation, that its clauses are pairwise *exclusive* on the inputs (their heads
//! do not unify on the input positions; or they do, but their arithmetic premises contradict
//! each other; or some premise then has no clause that can apply, to a small depth; or the
//! two clauses agree, with the same outputs and premises on the overlap). Together these say
//! the relation is a partial function computed deterministically by the prover (`horn`): no
//! clause can give a second output. The pairs that overlap by design are listed
//! ([`OVERLAPS`]) with the reason the overlap is harmless, and the check requires the list to
//! be exact.
//!
//! A position marked `*` is an input given up to its head: a term whose head is a
//! constructor other than `app` (`spine (ind_ty D j) e k` finds `k`, where `spine h e k` with
//! `h` unknown would not be a function of `e`).
use crate::bail;
use crate::env::*;
use crate::horn::{Horn, Index};
use rustc_hash::FxHashMap as HashMap;
use std::fmt::Write;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// The graph of a function: exclusive clauses.
    Fn,
    /// A predicate: every position an input.
    Check,
    /// Clauses tried in order; the output depends on the order. Not exclusive.
    Search,
}

/// Kind and modes of every relation of the spec other than the rule heads (`deq`, `leqv`,
/// `inh`) and the builtins `add` (any two arguments determine the third) and `le`. A
/// checking relation's mode is every position an input (`""`); a computing relation may
/// have several modes, separated by `|`.
pub const TABLE: &[(&str, Kind, &str)] = &[
    // naturals and levels
    ("le", Kind::Check, ""),
    ("lnth", Kind::Fn, "++-"),
    ("linst", Kind::Fn, "++-"),
    ("lsubst", Kind::Fn, "+++-"),
    // expressions and contexts
    ("closed", Kind::Check, ""),
    ("lift", Kind::Fn, "+++-"),
    ("inst", Kind::Fn, "+++-"),
    ("lookup", Kind::Fn, "++-"),
    ("cinst", Kind::Fn, "+--++-"),
    ("cext", Kind::Fn, "+-+"),
    // binary arithmetic
    ("bsucc", Kind::Fn, "+-"),
    ("bdbl", Kind::Fn, "+-"),
    ("badd", Kind::Fn, "++-"),
    ("baddc", Kind::Fn, "++-"),
    ("bmul", Kind::Fn, "++-"),
    ("bpow", Kind::Fn, "++-"),
    ("band", Kind::Fn, "++-"),
    ("bor", Kind::Fn, "++-"),
    ("bxor", Kind::Fn, "++-"),
    // inductive blocks: reading the data
    ("ind_data", Kind::Fn, "+---"),
    ("nth_ty", Kind::Fn, "++--"),
    ("nth_ctor", Kind::Fn, "++-"),
    ("clen", Kind::Fn, "+-"),
    ("cnth", Kind::Fn, "++-"),
    ("clen_c", Kind::Fn, "+-"),
    ("ntys", Kind::Fn, "+--"),
    ("minor_idx", Kind::Fn, "+++-"),
    ("npis", Kind::Fn, "+-"),
    ("nth_pi", Kind::Fn, "++-"),
    ("isort", Kind::Fn, "+--"),
    ("ind_arity", Kind::Fn, "+---"),
    ("nidx", Kind::Fn, "++-"),
    ("nfields", Kind::Fn, "+++-"),
    // telescopes and applications
    ("pis", Kind::Fn, "++-"),
    ("lams", Kind::Fn, "++-"),
    ("tys_closed", Kind::Check, ""),
    ("capp", Kind::Fn, "++-"),
    ("clift", Kind::Fn, "++-"),
    ("pargs", Kind::Fn, "+++-"),
    ("rehead", Kind::Fn, "-+++-"),
    ("spine", Kind::Fn, "-++|*+-"),
    ("has_arg", Kind::Check, ""),
    ("pinst", Kind::Fn, "+++-"),
    // well-formedness
    ("sinst", Kind::Fn, "+++++-"),
    ("iargs", Kind::Check, ""),
    ("indapp", Kind::Fn, "+++++-"),
    ("ipos", Kind::Check, ""),
    ("recfield", Kind::Fn, "+++++-"),
    ("ulevel", Kind::Check, ""),
    ("cwf", Kind::Check, ""),
    ("ctors_wf", Kind::Check, ""),
    ("tys_wf", Kind::Check, ""),
    ("ctx_wf", Kind::Check, ""),
    ("tys_ty", Kind::Check, ""),
    ("tys_ok", Kind::Check, ""),
    ("ind_wf", Kind::Check, ""),
    // nested blocks
    ("ind_nested", Kind::Fn, "+-"),
    ("ndecl", Kind::Fn, "++-"),
    ("aux_of", Kind::Fn, "+++-"),
    ("rst", Kind::Search, "+++-"),
    ("nst_hit", Kind::Check, ""),
    ("spz", Kind::Check, ""),
    ("afree", Kind::Check, ""),
    ("spz_ctors", Kind::Check, ""),
    ("aux_data", Kind::Check, ""),
    ("nst_ty", Kind::Check, ""),
    ("nst_ok", Kind::Check, ""),
    ("nst_group", Kind::Fn, "++++++++-"),
    // the elimination level
    ("large", Kind::Check, ""),
    ("fir", Kind::Check, ""),
    ("leaf_has", Kind::Check, ""),
    ("elim_ok", Kind::Check, ""),
    // the recursor's type and rules
    ("mty", Kind::Fn, "++++++-"),
    ("motives", Kind::Fn, "+++++-"),
    ("ihty", Kind::Fn, "++++++++-"),
    ("mwalk", Kind::Fn, "+++++++++++-"),
    ("cminors", Kind::Fn, "+++++++-"),
    ("minors", Kind::Fn, "++++++-"),
    ("rtail", Kind::Fn, "+++++++-"),
    ("rec_ty", Kind::Fn, "+++-"),
    ("ctor_ty", Kind::Fn, "+++-"),
    ("ihval", Kind::Fn, "++++++++++-"),
    ("rwalk", Kind::Fn, "+++++++++-"),
    ("rec_rhs", Kind::Fn, "++++-"),
    // structures
    ("struct_like", Kind::Check, ""),
    ("field_ty", Kind::Fn, "+++-"),
    ("fprops", Kind::Check, ""),
    ("proj_ok", Kind::Check, ""),
    ("qinst", Kind::Fn, "+++++-"),
    ("nonrec", Kind::Check, ""),
    ("eta_ok", Kind::Check, ""),
    ("projs", Kind::Fn, "++++-"),
    // typed application spines: the head given up to its head constructor (a head that is
    // itself an application would make `sty_nil` and `sty_app` overlap)
    ("sty", Kind::Fn, "+*++-"),
    // spines with definitionally equal arguments
    ("aeq", Kind::Check, ""),
    // level equivalence of expressions
    ("eeqv", Kind::Check, ""),
    ("lseqv", Kind::Check, ""),
    ("ind_eqv", Kind::Check, ""),
    ("ceqv", Kind::Check, ""),
    ("teqv", Kind::Check, ""),
    ("cseqv", Kind::Check, ""),
    // the literal operations' equations
    ("add_eqs", Kind::Check, ""),
    ("pred_eqs", Kind::Check, ""),
    ("sub_eqs", Kind::Check, ""),
    ("mul_eqs", Kind::Check, ""),
    ("pow_eqs", Kind::Check, ""),
    ("beq_eqs", Kind::Check, ""),
    ("ble_eqs", Kind::Check, ""),
    ("shl_eqs", Kind::Check, ""),
    ("shr_eqs", Kind::Check, ""),
    ("dec_eqs", Kind::Check, ""),
    ("ite_eqs", Kind::Check, ""),
    ("natle_dec", Kind::Check, ""),
    ("nateq_dec", Kind::Check, ""),
    ("bool_dec", Kind::Check, ""),
    ("div_eqs", Kind::Check, ""),
    ("mod_eqs", Kind::Check, ""),
    ("fix_eqs", Kind::Check, ""),
    ("gcd_eqs", Kind::Check, ""),
    ("bitwise_eqs", Kind::Check, ""),
    ("bitop_eqs", Kind::Check, ""),
];

/// The heads of the rules: axioms with these heads are the theory, not definitions.
pub const RULE_HEADS: &[&str] = &["deq", "leqv", "inh"];

/// Pairs of clauses of a computing relation that overlap on their inputs by design, with the
/// reason that both give the same output. The check requires every overlap it cannot resolve
/// to be listed here, and every pair listed here to overlap.
pub const OVERLAPS: &[(&str, &str, &str)] = &[
    ("lift_closed", "*", "admissible: lifting a closed term is the identity, which the structural clauses compute too (`ClosedN.liftN_eq`)"),
    ("inst_closed", "*", "admissible: instantiating a closed term is the identity, which the structural clauses compute too (`ClosedN.instN_eq`)"),
    ("mwalk_pi_nr", "mwalk_pi_rec", "a recursive field (`recfield`: the block applied to its parameters, under binders) is not `closed` above the parameters"),
    ("rwalk_pi_nr", "rwalk_pi_rec", "a recursive field (`recfield`) is not `closed` above the parameters"),
];

struct Rel {
    kind: Kind,
    /// Each mode: a flag per argument (`'+'`, `'-'`, `'*'`).
    modes: Vec<Vec<u8>>,
    clauses: Vec<ThId>,
}

/// The report: one line per relation, then the errors. `ok` is false if any error.
pub struct Report {
    pub text: String,
    pub errors: Vec<String>,
}

const REFUTE_DEPTH: usize = 4;
const REFUTE_BUDGET: usize = 20_000;

pub fn check(spec: &str) -> Result<Report> {
    let mut env = Env::new();
    crate::parse::parse_into(&mut env, spec)?;
    let mut errors = Vec::new();
    let mut text = String::new();
    let wff = env.sort_names["wff"];

    // the relations: every `term` of sort `wff` that is not a rule head
    let mut rels: Vec<(TId, Rel)> = Vec::new();
    let mut by_tid: HashMap<TId, usize> = HashMap::default();
    for (i, t) in env.terms.iter().enumerate() {
        if t.ret != wff || !matches!(t.kind, TermKind::Term) || RULE_HEADS.contains(&t.name.as_str()) || t.name == "add" {
            continue
        }
        let Some(&(_, kind, modes)) = TABLE.iter().find(|(n, _, _)| *n == t.name) else {
            errors.push(format!("{}: no kind and mode declared (modes::TABLE)", t.name));
            continue
        };
        let modes: Vec<Vec<u8>> = if kind == Kind::Check { vec![vec![b'+'; t.args.len()]] } else { modes.split('|').map(|m| m.bytes().collect()).collect() };
        for m in &modes {
            if m.len() != t.args.len() || m.iter().any(|c| !b"+-*".contains(c)) {
                errors.push(format!("{}: the mode `{}` does not fit {} arguments", t.name, String::from_utf8_lossy(m), t.args.len()));
            }
        }
        by_tid.insert(TId(i as u32), rels.len());
        rels.push((TId(i as u32), Rel { kind, modes, clauses: Vec::new() }));
    }
    for (name, _, _) in TABLE {
        if !env.has_term(name) {
            errors.push(format!("{name}: in modes::TABLE but not in the spec"));
        }
    }
    let ids = Ids {
        add: env.term_id("add"),
        le: env.term_id("le"),
        s: env.term_id("s"),
        z: env.term_id("nz"),
        lift: env.term_id("lift"),
        inst: env.term_id("inst"),
        bvar: env.term_id("bvar"),
        app: env.term_id("app"),
        nat: env.sort_names["nat"],
        rule_heads: RULE_HEADS.iter().map(|n| env.term_id(n)).collect(),
    };
    // the clauses, in order; the rules are counted
    let mut n_rules = 0;
    let mut counts = [0usize; 3];
    for i in 0..env.thms.len() {
        let d = env.thms[i].clone();
        // a conclusion through a definition (`ty`) is read unfolded
        let mut concl = d.concl;
        while let Some(c2) = env.unfold(concl) {
            concl = c2;
        }
        let Some((h, _)) = env.head(concl) else { continue };
        if let Some(&r) = by_tid.get(&h) {
            rels[r].1.clauses.push(ThId(i as u32));
        } else if ids.rule_heads.contains(&h) {
            n_rules += 1;
        } else if h == ids.add {
            counts[Kind::Fn as usize] += 1; // the builtin
        } else {
            errors.push(format!("{}: concludes `{}`, which is neither a relation nor a rule head", d.name, env.terms[h.0 as usize].name));
        }
    }

    // an opaque term per sort, standing for an argument given up to its head (`*`)
    let mut opaque: HashMap<u8, TId> = HashMap::default();
    for s in 0..env.sorts.len() {
        let t = env.add_term(TermDecl { name: format!("?head_{}", env.sorts[s].name), args: vec![], ret: s as u8, kind: TermKind::Term, local: true, doc: None })?;
        opaque.insert(s as u8, t);
    }

    let ix = Index::new(&env);
    let mut n_overlaps_used = vec![false; OVERLAPS.len()];
    for (t, rel) in &rels {
        let name = env.terms[t.0 as usize].name.clone();
        counts[rel.kind as usize] += rel.clauses.len();
        // well-modedness of each clause
        for &c in &rel.clauses {
            for m in &rel.modes {
                if let Err(e) = well_moded(&mut env, &ids, &rels, &by_tid, c, rel.kind, m) {
                    errors.push(format!("{}: {}", env.thms[c.0 as usize].name, e.0));
                }
            }
        }
        let mut status = String::new();
        if rel.kind == Kind::Fn {
            let mut n_guard = 0;
            let mut n_agree = 0;
            let mut listed = Vec::new();
            for m in rel.modes.iter() {
                for i in 0..rel.clauses.len() {
                    for j in i + 1..rel.clauses.len() {
                        let (a, b) = (rel.clauses[i], rel.clauses[j]);
                        let (na, nb) = (env.thms[a.0 as usize].name.to_string(), env.thms[b.0 as usize].name.to_string());
                        let mut h = Horn::with_index(ix.clone());
                        h.occurs_check = true;
                        let r = exclusive(&mut h, &mut env, &ids, &rels, &by_tid, &opaque, a, b, m);
                        let listed_at = OVERLAPS.iter().position(|(x, y, _)| (*x == na && (*y == nb || *y == "*")) || (*x == nb && (*y == na || *y == "*")));
                        match r {
                            Exclusive::Heads => {}
                            Exclusive::Guards => n_guard += 1,
                            Exclusive::Agree => n_agree += 1,
                            Exclusive::Overlap => match listed_at {
                                Some(k) => {
                                    n_overlaps_used[k] = true;
                                    if !listed.contains(&k) {
                                        listed.push(k);
                                    }
                                }
                                None => errors.push(format!(
                                    "{name}: the clauses {na} and {nb} overlap on the inputs (mode {}) and are not listed in modes::OVERLAPS",
                                    String::from_utf8_lossy(m)
                                )),
                            },
                        }
                    }
                }
            }
            status.push_str("exclusive");
            if n_guard > 0 {
                write!(status, ", {n_guard} by guards").unwrap();
            }
            if n_agree > 0 {
                write!(status, ", {n_agree} agreeing").unwrap();
            }
            for k in listed {
                write!(status, "; {} / {}: {}", OVERLAPS[k].0, OVERLAPS[k].1, OVERLAPS[k].2).unwrap();
            }
        }
        let kind = match rel.kind {
            Kind::Fn => "fn",
            Kind::Check => "check",
            Kind::Search => "search",
        };
        let modes: Vec<String> = rel.modes.iter().map(|m| String::from_utf8_lossy(m).into_owned()).collect();
        writeln!(text, "{name:12} {kind:6} {:14} {:3} clauses  {status}", modes.join("|"), rel.clauses.len()).unwrap();
    }
    for (k, used) in n_overlaps_used.iter().enumerate() {
        if !used {
            errors.push(format!("modes::OVERLAPS lists {} / {}, which do not overlap", OVERLAPS[k].0, OVERLAPS[k].1));
        }
    }
    writeln!(text, "{} relations: {} computing clauses, {} checking clauses, {} search clauses; {} rules", rels.len(), counts[0], counts[1], counts[2], n_rules).unwrap();
    Ok(Report { text, errors })
}

struct Ids {
    add: TId,
    le: TId,
    s: TId,
    z: TId,
    lift: TId,
    inst: TId,
    bvar: TId,
    app: TId,
    nat: u8,
    rule_heads: Vec<TId>,
}

fn vars_of(env: &Env, e: E, out: &mut Vec<u16>) {
    match env.node(e) {
        Node::Var(i) => {
            if !out.contains(&i) {
                out.push(i)
            }
        }
        Node::Meta(_) => {}
        Node::App(_, xs) => {
            for &x in xs.to_vec().iter() {
                vars_of(env, x, out)
            }
        }
    }
}

/// A term given up to its head: a constructor other than `app`, or fully determined.
fn head_given(env: &Env, ids: &Ids, e: E, det: &[bool]) -> bool {
    let mut vs = Vec::new();
    vars_of(env, e, &mut vs);
    if vs.iter().all(|&v| det[v as usize]) {
        return true
    }
    matches!(env.head(e), Some((t, _)) if t != ids.app)
}

/// Determinedness: the clause's input variables are given; a premise fires when its inputs
/// are determined, and determines its outputs. Errors: an output of the clause, or an input
/// of a computing premise, that is never determined.
fn well_moded(env: &mut Env, ids: &Ids, rels: &[(TId, Rel)], by_tid: &HashMap<TId, usize>, c: ThId, kind: Kind, mode: &[u8]) -> Result<()> {
    let d = env.thms[c.0 as usize].clone();
    let names: Vec<&str> = d.args.iter().map(|(n, _)| n.as_str()).collect();
    let mut det = vec![false; d.args.len()];
    let (_, hargs) = env.head(d.concl).unwrap();
    let hargs = hargs.to_vec();
    let mark = |env: &Env, e: E, det: &mut Vec<bool>| {
        let mut vs = Vec::new();
        vars_of(env, e, &mut vs);
        for v in vs {
            det[v as usize] = true;
        }
    };
    for (i, &a) in hargs.iter().enumerate() {
        if mode[i] != b'-' {
            mark(env, a, &mut det);
        }
    }
    let mut fired = vec![false; d.hyps.len()];
    loop {
        let mut progress = false;
        for (hi, &h) in d.hyps.iter().enumerate() {
            if fired[hi] {
                continue
            }
            let Some((t, args)) = env.head(h) else { bail!("a premise is a variable") };
            let args = args.to_vec();
            let all_det = |env: &Env, e: E, det: &[bool]| {
                let mut vs = Vec::new();
                vars_of(env, e, &mut vs);
                vs.iter().all(|&v| det[v as usize])
            };
            if t == ids.add {
                let n = args.iter().filter(|&&a| all_det(env, a, &det)).count();
                if n >= 2 {
                    for &a in &args {
                        mark(env, a, &mut det);
                    }
                    fired[hi] = true;
                    progress = true;
                }
                continue
            }
            let Some(&r) = by_tid.get(&t) else {
                // a rule head (`deq`, `leqv`, ...), `le`, or a definition: a side condition
                fired[hi] = true;
                progress = true;
                continue
            };
            let rel = &rels[r].1;
            for m in &rel.modes {
                let ok = m.iter().zip(&args).all(|(&f, &a)| match f {
                    b'+' => all_det(env, a, &det),
                    b'*' => head_given(env, ids, a, &det),
                    _ => true,
                });
                if ok {
                    for (&f, &a) in m.iter().zip(&args) {
                        if f != b'+' {
                            mark(env, a, &mut det);
                        }
                    }
                    fired[hi] = true;
                    progress = true;
                    break
                }
            }
        }
        if !progress {
            break
        }
    }
    let mut problems = Vec::new();
    for (hi, &h) in d.hyps.iter().enumerate() {
        if !fired[hi] {
            let (t, _) = env.head(h).unwrap();
            if t == ids.add || rels[by_tid[&t]].1.kind != Kind::Check {
                problems.push(format!("the premise `{}` is used as a search (its inputs are not determined)", env.show(h, &names)));
            }
        }
    }
    if kind != Kind::Check {
        for (i, &a) in hargs.iter().enumerate() {
            if mode[i] == b'-' {
                let mut vs = Vec::new();
                vars_of(env, a, &mut vs);
                for v in vs {
                    if !det[v as usize] {
                        problems.push(format!("the output `{}` is not determined by the inputs (mode {})", names[v as usize], String::from_utf8_lossy(mode)));
                    }
                }
            }
        }
    }
    if problems.is_empty() { Ok(()) } else { Err(Mm0Error(problems.join("; "))) }
}

enum Exclusive {
    /// The heads do not unify on the inputs.
    Heads,
    /// They do, but the premises cannot all hold.
    Guards,
    /// They do, with the same outputs and premises.
    Agree,
    Overlap,
}

#[allow(clippy::too_many_arguments)]
fn exclusive(h: &mut Horn, env: &mut Env, ids: &Ids, rels: &[(TId, Rel)], by_tid: &HashMap<TId, usize>, opaque: &HashMap<u8, TId>, a: ThId, b: ThId, mode: &[u8]) -> Exclusive {
    let (da, db) = (env.thms[a.0 as usize].clone(), env.thms[b.0 as usize].clone());
    let fresh = |h: &mut Horn, env: &mut Env, d: &ThmDecl| -> Vec<E> { (0..d.args.len()).map(|_| h.meta(env)).collect() };
    let (ma, mb) = (fresh(h, env, &da), fresh(h, env, &db));
    let (ca, cb) = (env.subst(da.concl, &ma), env.subst(db.concl, &mb));
    let (under_test, xa) = env.head(ca).unwrap();
    let xa = xa.to_vec();
    let (_, xb) = env.head(cb).unwrap();
    let xb = xb.to_vec();
    let sorts: Vec<u8> = env.terms[under_test.0 as usize].args.iter().map(|(_, s)| *s).collect();
    // `*`: the argument has a head other than `app`; a bare variable stands for any such term
    for (i, &f) in mode.iter().enumerate() {
        if f == b'*' {
            for &x in [xa[i], xb[i]].iter() {
                let zx = h.zonk(env, x);
                if matches!(env.node(zx), Node::Meta(_)) {
                    let o = env.app(opaque[&sorts[i]], &[]);
                    h.unify(env, x, o);
                }
            }
        }
    }
    for (i, &f) in mode.iter().enumerate() {
        if f != b'-' && !h.unify(env, xa[i], xb[i]) {
            return Exclusive::Heads
        }
    }
    let mut goals: Vec<E> = da.hyps.iter().map(|&p| env.subst(p, &ma)).collect();
    for &p in db.hyps.iter() {
        let g = env.subst(p, &mb);
        goals.push(g);
    }
    // in textual order, the first clause's premises first (popped from the end)
    let stack: Vec<(E, usize)> = goals.iter().rev().map(|&g| (g, 0)).collect();
    let mut budget = REFUTE_BUDGET;
    let saved = h.save();
    let refuted = refute(h, env, ids, rels, by_tid, under_test, stack, Vec::new(), &mut budget);
    h.restore(saved);
    if refuted {
        return Exclusive::Guards
    }
    // agreement: the outputs unify and the premises are the same
    let saved = h.save();
    let outputs_agree = mode.iter().enumerate().all(|(i, &f)| f != b'-' || h.unify(env, xa[i], xb[i]));
    if outputs_agree {
        let mut pa: Vec<E> = goals.drain(..da.hyps.len()).map(|g| h.zonk(env, g)).collect();
        let mut pb: Vec<E> = goals.drain(..).map(|g| h.zonk(env, g)).collect();
        pa.sort();
        pb.sort();
        if pa == pb {
            h.restore(saved);
            return Exclusive::Agree
        }
    }
    h.restore(saved);
    Exclusive::Overlap
}

/// A difference constraint `x - y <= c` on nat terms, each a variable (a metavariable's id)
/// or zero (`None`) plus an offset.
type Nat = (Option<u32>, i64);
type Constraint = (Nat, Nat, i64);

fn nat_term(h: &mut Horn, env: &mut Env, ids: &Ids, e: E) -> Option<Nat> {
    let mut e = h.zonk(env, e);
    let mut n = 0;
    loop {
        match env.node(e) {
            Node::Meta(i) => return Some((Some(i), n)),
            Node::App(t, xs) if t == ids.s => {
                e = xs[0];
                n += 1;
            }
            Node::App(t, _) if t == ids.z => return Some((None, n)),
            // a numeral `n3`
            Node::App(t, _) if env.is_def(t) => e = env.unfold(e)?,
            _ => return None,
        }
    }
}

/// `a <= b` as a constraint: `xa + ca <= xb + cb`, i.e. `xa - xb <= cb - ca`.
fn le_constraint(a: Nat, b: Nat) -> Constraint { (a, b, b.1 - a.1) }

/// Unsatisfiable: a negative cycle (Bellman-Ford), with every variable at least zero.
fn unsat(cs: &[Constraint]) -> bool {
    let mut nodes: Vec<Option<u32>> = vec![None];
    for (a, b, _) in cs {
        for x in [a.0, b.0] {
            if !nodes.contains(&x) {
                nodes.push(x);
            }
        }
    }
    let idx = |x: Option<u32>| nodes.iter().position(|&n| n == x).unwrap();
    // edges: x - y <= c is an edge y -> x of weight c; x >= 0 is 0 - x <= 0: edge x -> 0
    let mut edges: Vec<(usize, usize, i64)> = cs.iter().map(|&(a, b, c)| (idx(b.0), idx(a.0), c)).collect();
    for i in 1..nodes.len() {
        edges.push((i, 0, 0));
    }
    let mut dist = vec![0i64; nodes.len()];
    for _ in 0..nodes.len() {
        let mut changed = false;
        for &(u, v, w) in &edges {
            if dist[u] + w < dist[v] {
                dist[v] = dist[u] + w;
                changed = true;
            }
        }
        if !changed {
            return false
        }
    }
    true
}

/// True if the goals cannot all hold: every way of applying clauses to them fails. Each
/// goal is tried in turn, with its clauses' premises as new goals one level deeper; a goal
/// deeper than `REFUTE_DEPTH`, a goal of the relation under test (an induction hypothesis),
/// a goal with nothing to match on (every non-numeral input a bare metavariable), and a goal
/// of a relation this does not reason about count as satisfiable, as does an exhausted
/// budget: unknown never refutes. `cs` are the arithmetic constraints met so far.
#[allow(clippy::too_many_arguments)]
fn refute(h: &mut Horn, env: &mut Env, ids: &Ids, rels: &[(TId, Rel)], by_tid: &HashMap<TId, usize>, under_test: TId, mut goals: Vec<(E, usize)>, mut cs: Vec<Constraint>, budget: &mut usize) -> bool {
    loop {
        if *budget == 0 {
            return false
        }
        *budget -= 1;
        let Some((g, nest)) = goals.pop() else { return false };
        let g = h.zonk(env, g);
        let Some((t, args)) = env.head(g) else { return false };
        let args = args.to_vec();
        if t == ids.le || t == ids.add {
            let ns: Vec<Option<Nat>> = args.iter().map(|&a| nat_term(h, env, ids, a)).collect();
            if ns.iter().any(|n| n.is_none()) {
                continue
            }
            let ns: Vec<Nat> = ns.into_iter().map(|n| n.unwrap()).collect();
            if t == ids.le {
                cs.push(le_constraint(ns[0], ns[1]));
            } else {
                // i + n = j
                let (i, n, j) = (ns[0], ns[1], ns[2]);
                if i.0.is_none() {
                    cs.push(le_constraint((n.0, n.1 + i.1), j));
                    cs.push(le_constraint(j, (n.0, n.1 + i.1)));
                } else if n.0.is_none() {
                    cs.push(le_constraint((i.0, i.1 + n.1), j));
                    cs.push(le_constraint(j, (i.0, i.1 + n.1)));
                } else {
                    cs.push(le_constraint(i, j));
                    cs.push(le_constraint(n, j));
                }
            }
            if unsat(&cs) {
                return true
            }
            continue
        }
        if t == ids.lift || t == ids.inst {
            // the result has the shape of the argument, except at a variable
            let (e, e2) = if t == ids.lift { (args[2], args[3]) } else { (args[1], args[3]) };
            let ze = h.zonk(env, e);
            if let Some((c, xs)) = env.head(ze) {
                if c != ids.bvar {
                    let n = xs.len();
                    let ys: Vec<E> = (0..n).map(|_| h.meta(env)).collect();
                    let shape = env.app(c, &ys);
                    if !h.unify(env, e2, shape) {
                        return true
                    }
                }
            }
            continue
        }
        // a definition (`lt`, `ty`): its unfolding
        if let Some(g2) = env.unfold(g) {
            goals.push((g2, nest));
            continue
        }
        // a rule head (`deq`, `leqv`) or a builtin: not reasoned about
        let Some(&r) = by_tid.get(&t) else { continue };
        if t == under_test || nest > REFUTE_DEPTH {
            continue
        }
        let rel = &rels[r].1;
        let sorts: Vec<u8> = env.terms[t.0 as usize].args.iter().map(|(_, s)| *s).collect();
        let zargs: Vec<E> = args.iter().map(|&a| h.zonk(env, a)).collect();
        let nothing_to_match = rel.modes[0].iter().zip(&zargs).zip(&sorts).all(|((&f, &a), &s)| {
            f == b'-' || s == ids.nat || matches!(env.node(a), Node::Meta(_))
        });
        if nothing_to_match {
            continue
        }
        // every clause must fail
        for &c in &rel.clauses {
            let d = env.thms[c.0 as usize].clone();
            let saved = h.save();
            let metas: Vec<E> = (0..d.args.len()).map(|_| h.meta(env)).collect();
            let concl = env.subst(d.concl, &metas);
            if h.unify(env, concl, g) {
                let mut goals2 = goals.clone();
                for &p in d.hyps.iter().rev() {
                    let p2 = env.subst(p, &metas);
                    goals2.push((p2, nest + 1));
                }
                let ok = refute(h, env, ids, rels, by_tid, under_test, goals2, cs.clone(), budget);
                h.restore(saved);
                if !ok {
                    return false
                }
            } else {
                h.restore(saved);
            }
        }
        return true
    }
}
