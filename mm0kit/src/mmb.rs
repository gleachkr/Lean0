//! Writing an `Env` as an MMB file (format: `mm0-c/mmb.md`, version 1).
//!
//! Every statement in `Env::order` is written; public ones must line up with the `.mm0` file
//! produced by `Env::stmt_text`. Expressions are shared on the heap whenever they occur more
//! than once in a statement, and so are proofs.

use crate::env::*;
use rustc_hash::FxHashMap as HashMap;

mod cmd {
    pub const UTERM: u8 = 0x30;
    pub const UTERM_SAVE: u8 = 0x31;
    pub const UREF: u8 = 0x32;
    pub const UHYP: u8 = 0x36;
    pub const TERM: u8 = 0x10;
    pub const TERM_SAVE: u8 = 0x11;
    pub const REF: u8 = 0x12;
    pub const THM: u8 = 0x14;
    pub const THM_SAVE: u8 = 0x15;
    pub const HYP: u8 = 0x16;
    pub const CONV: u8 = 0x17;
    pub const REFL: u8 = 0x18;
    pub const SYM: u8 = 0x19;
    pub const CONG: u8 = 0x1A;
    pub const UNFOLD: u8 = 0x1B;
    pub const SAVE: u8 = 0x1F;
    pub const ST_SORT: u8 = 0x04;
    pub const ST_TERM: u8 = 0x05;
    pub const ST_LOCAL_DEF: u8 = 0x0D;
    pub const ST_AXIOM: u8 = 0x02;
    pub const ST_THM: u8 = 0x06;
    pub const ST_LOCAL_THM: u8 = 0x0E;
}

fn push_cmd(out: &mut Vec<u8>, c: u8, data: u32) {
    if data == 0 {
        out.push(c);
    } else if data <= 0xff {
        out.extend([0x40 | c, data as u8]);
    } else if data <= 0xffff {
        out.push(0x80 | c);
        out.extend((data as u16).to_le_bytes());
    } else {
        out.push(0xC0 | c);
        out.extend(data.to_le_bytes());
    }
}

/// Encode the statement header for a statement whose body has `body_len` bytes.
fn stmt_header(c: u8, body_len: usize) -> Vec<u8> {
    for hdr in [2usize, 3, 5] {
        let total = hdr + body_len;
        let fits = match hdr {
            2 => total <= 0xff,
            3 => total <= 0xffff,
            _ => true,
        };
        if fits {
            let mut out = Vec::new();
            match hdr {
                2 => out.extend([0x40 | c, total as u8]),
                3 => {
                    out.push(0x80 | c);
                    out.extend((total as u16).to_le_bytes());
                }
                _ => {
                    out.push(0xC0 | c);
                    out.extend(u32::try_from(total).unwrap().to_le_bytes());
                }
            }
            return out
        }
    }
    unreachable!()
}

fn arg_u64(sort: u8) -> u64 { (sort as u64) << 56 }

/// Count how often each expression is visited by a traversal that does not re-enter shared
/// nodes, so the emitter knows which ones to save.
fn count_expr(env: &Env, e: E, counts: &mut HashMap<E, u32>) {
    let c = counts.entry(e).or_insert(0);
    *c += 1;
    if *c > 1 {
        return
    }
    if let Node::App(_, args) = env.node(e) {
        for &a in args.iter() {
            count_expr(env, a, counts);
        }
    }
}

/// Unify stream of an expression (Polish order).
struct Unify<'a> {
    env: &'a Env,
    counts: HashMap<E, u32>,
    heap: HashMap<E, u32>,
    next: u32,
    out: Vec<u8>,
}

impl Unify<'_> {
    fn new<'a>(env: &'a Env, nargs: usize, exprs: &[E]) -> Unify<'a> {
        let mut counts = HashMap::default();
        for &e in exprs {
            count_expr(env, e, &mut counts);
        }
        Unify { env, counts, heap: HashMap::default(), next: nargs as u32, out: Vec::new() }
    }

    fn expr(&mut self, e: E) {
        match self.env.node(e) {
            Node::Var(i) => push_cmd(&mut self.out, cmd::UREF, i as u32),
            Node::Meta(_) => panic!("a metavariable in a statement"),
            Node::App(t, args) => {
                if let Some(&h) = self.heap.get(&e) {
                    push_cmd(&mut self.out, cmd::UREF, h);
                    return
                }
                if self.counts[&e] > 1 {
                    push_cmd(&mut self.out, cmd::UTERM_SAVE, t.0);
                    self.heap.insert(e, self.next);
                    self.next += 1;
                } else {
                    push_cmd(&mut self.out, cmd::UTERM, t.0);
                }
                for &a in args.iter() {
                    self.expr(a);
                }
            }
        }
    }
}

/// The table data of a term or theorem: its argument array (and return sort), then the unify
/// stream of its def body or of its conclusion and hypotheses.
fn table_bytes(env: &Env, args: &[(String, u8)], ret: Option<u8>, exprs: &[E], hyps: &[E]) -> Vec<u8> {
    let mut b = Vec::new();
    for a in args {
        b.extend(arg_u64(a.1).to_le_bytes());
    }
    if let Some(r) = ret {
        b.extend(arg_u64(r).to_le_bytes());
    }
    let mut all = exprs.to_vec();
    all.extend(hyps.iter().rev());
    let mut u = Unify::new(env, args.len(), &all);
    for &e in exprs {
        u.expr(e);
    }
    for &h in hyps.iter().rev() {
        push_cmd(&mut u.out, cmd::UHYP, 0);
        u.expr(h);
    }
    u.out.push(0);
    b.extend(u.out);
    b
}

fn stmt_name(env: &Env, st: Stmt) -> &str {
    match st {
        Stmt::Sort(s) => env.sorts[s as usize].name.as_str(),
        Stmt::Term(t) => env.terms[t.0 as usize].name.as_str(),
        Stmt::Thm(t) => env.thms[t.0 as usize].name.as_ref(),
    }
}

/// A lemma made while proving (named with `lean::FACT_PREFIX`): sharded generation writes it
/// in whichever shard made it, and the merge keeps one copy of each statement.
fn is_lemma(env: &Env, st: Stmt) -> bool {
    matches!(st, Stmt::Thm(t) if env.thms[t.0 as usize].name.starts_with(crate::lean::FACT_PREFIX))
}

/// A statement as written: its command, name, argument count, flags (a term's return sort and
/// def bit, or a sort's modifiers), table data and proof-stream body (without the header).
struct Raw {
    kind: Stmt,
    cmd: u8,
    name: String,
    nargs: u16,
    flags: u8,
    table: Vec<u8>,
    body: Vec<u8>,
}

fn kind_code(st: Stmt) -> u8 {
    match st {
        Stmt::Sort(_) => 0,
        Stmt::Term(_) => 1,
        Stmt::Thm(_) => 2,
    }
}

/// The statements of one shard of a sharded generation, in order: each is either written here
/// (`owned`) or a reference to the statement that the shard owning its declaration writes
/// (`foreign`), found there by its position among that declaration's statements other than
/// lemmas. Records: tag (0 owned, 1 foreign), declaration index (u32), kind (0 sort, 1 term,
/// 2 theorem), name; and for owned ones the command, argument count (u16), flags, table data
/// and body (each u32-length-prefixed). See `merge`.
pub struct ShardOut {
    w: std::io::BufWriter<std::fs::File>,
}

impl ShardOut {
    pub fn create(path: &std::path::Path) -> std::io::Result<ShardOut> {
        Ok(ShardOut { w: std::io::BufWriter::with_capacity(1 << 20, std::fs::File::create(path)?) })
    }

    fn head(&mut self, tag: u8, decl: u32, st: Stmt, name: &str) -> std::io::Result<()> {
        use std::io::Write;
        self.w.write_all(&[tag])?;
        self.w.write_all(&decl.to_le_bytes())?;
        self.w.write_all(&[kind_code(st)])?;
        self.bytes(name.as_bytes())
    }

    fn bytes(&mut self, b: &[u8]) -> std::io::Result<()> {
        use std::io::Write;
        self.w.write_all(&u32::try_from(b.len()).unwrap().to_le_bytes())?;
        self.w.write_all(b)
    }

    fn foreign(&mut self, decl: u32, st: Stmt, name: &str) -> std::io::Result<()> { self.head(1, decl, st, name) }

    fn owned(&mut self, decl: u32, r: &Raw) -> std::io::Result<()> {
        use std::io::Write;
        self.head(0, decl, r.kind, &r.name)?;
        self.w.write_all(&[r.cmd])?;
        self.w.write_all(&r.nargs.to_le_bytes())?;
        self.w.write_all(&[r.flags])?;
        self.bytes(&r.table)?;
        self.bytes(&r.body)
    }

    pub fn finish(mut self) -> std::io::Result<()> {
        use std::io::Write;
        self.w.flush()
    }
}

/// Proof stream of one statement.
struct Proof<'a> {
    env: &'a Env,
    ecounts: HashMap<E, u32>,
    pcounts: HashMap<P, u32>,
    eheap: HashMap<E, u32>,
    pheap: HashMap<P, u32>,
    hyps: Vec<u32>,
    next: u32,
    out: Vec<u8>,
    /// If set, bytes written by each (cost centre, rule) pair (see `ByteCosts`).
    tally: Option<&'a mut ByteCosts>,
}

/// Proof bytes by the cost centre and the rule of the proof node that wrote them (`LEAN0_COSTS`).
/// A node's bytes are its own command and the expressions it writes first; a reference to a
/// saved node counts as `REF_BYTES`. Rules are theorem ids below `spec_thms`, or one of the
/// buckets `LOCAL`, `GENERATED`, `CONV`, `REF_BYTES`.
#[derive(Default)]
pub struct ByteCosts {
    pub spec_thms: u32,
    pub bytes: HashMap<(u16, u32), u64>,
}

impl ByteCosts {
    pub const LOCAL: u32 = u32::MAX;
    pub const GENERATED: u32 = u32::MAX - 1;
    pub const CONV: u32 = u32::MAX - 2;
    pub const REF_BYTES: u32 = u32::MAX - 3;

    fn add(&mut self, env: &Env, p: P, rule: u32, n: usize) {
        let rule = match rule {
            r if r >= Self::REF_BYTES || r < self.spec_thms => r,
            r if env.thms[r as usize].local => Self::LOCAL,
            _ => Self::GENERATED,
        };
        *self.bytes.entry((env.pf_tag(p), rule)).or_default() += n as u64;
    }
}

impl<'a> Proof<'a> {
    fn new(env: &'a Env, nargs: usize) -> Self {
        Proof {
            env,
            ecounts: HashMap::default(),
            pcounts: HashMap::default(),
            eheap: HashMap::default(),
            pheap: HashMap::default(),
            hyps: Vec::new(),
            next: nargs as u32,
            out: Vec::new(),
            tally: None,
        }
    }

    // Counting pass: mirrors the emission order exactly.
    fn count_e(&mut self, e: E) {
        let c = self.ecounts.entry(e).or_insert(0);
        *c += 1;
        if *c > 1 {
            return
        }
        let env = self.env;
        if let Node::App(_, args) = env.node(e) {
            for &a in args.iter() {
                self.count_e(a);
            }
        }
    }

    fn count_cp(&mut self, cp: &Cp) {
        match cp {
            Cp::Refl => {}
            Cp::Cong(cps) => cps.iter().for_each(|c| self.count_cp(c)),
            Cp::UnfoldL(e, c) | Cp::UnfoldR(e, c) => {
                self.count_e(*e);
                self.count_cp(c);
            }
        }
    }

    fn count_p(&mut self, p: P) {
        let c = self.pcounts.entry(p).or_insert(0);
        *c += 1;
        if *c > 1 {
            return
        }
        match self.env.pf(p).clone() {
            Pf::Hyp(..) => {}
            Pf::Thm { hyps, args, concl, .. } => {
                for &h in hyps.iter() {
                    self.count_p(h);
                }
                for &a in args.iter() {
                    self.count_e(a);
                }
                self.count_e(concl);
            }
            Pf::Conv { target, from, cp } => {
                self.count_e(target);
                self.count_p(from);
                self.count_cp(&cp);
            }
        }
    }

    fn expr(&mut self, e: E) {
        let env = self.env;
        match env.node(e) {
            Node::Var(i) => push_cmd(&mut self.out, cmd::REF, i as u32),
            Node::Meta(_) => panic!("a metavariable in a proof"),
            Node::App(t, args) => {
                if let Some(&h) = self.eheap.get(&e) {
                    push_cmd(&mut self.out, cmd::REF, h);
                    return
                }
                for &a in args.iter() {
                    self.expr(a);
                }
                if self.ecounts.get(&e).copied().unwrap_or(1) > 1 {
                    push_cmd(&mut self.out, cmd::TERM_SAVE, t.0);
                    self.eheap.insert(e, self.next);
                    self.next += 1;
                } else {
                    push_cmd(&mut self.out, cmd::TERM, t.0);
                }
            }
        }
    }

    fn cp(&mut self, cp: &Cp) {
        match cp {
            Cp::Refl => push_cmd(&mut self.out, cmd::REFL, 0),
            Cp::Cong(cps) => {
                push_cmd(&mut self.out, cmd::CONG, 0);
                for c in cps.iter() {
                    self.cp(c);
                }
            }
            Cp::UnfoldL(e, c) => {
                self.expr(*e);
                push_cmd(&mut self.out, cmd::UNFOLD, 0);
                self.cp(c);
            }
            Cp::UnfoldR(e, c) => {
                push_cmd(&mut self.out, cmd::SYM, 0);
                self.expr(*e);
                push_cmd(&mut self.out, cmd::UNFOLD, 0);
                self.cp(c);
            }
        }
    }

    fn proof(&mut self, p: P) {
        if let Some(&h) = self.pheap.get(&p) {
            let n0 = self.out.len();
            push_cmd(&mut self.out, cmd::REF, h);
            if let Some(t) = &mut self.tally {
                t.add(self.env, p, ByteCosts::REF_BYTES, self.out.len() - n0);
            }
            return
        }
        let shared = self.pcounts.get(&p).copied().unwrap_or(1) > 1;
        match self.env.pf(p).clone() {
            Pf::Hyp(i, _) => {
                push_cmd(&mut self.out, cmd::REF, self.hyps[i as usize]);
                return
            }
            Pf::Thm { thm, args, hyps, concl } => {
                for &h in hyps.iter() {
                    self.proof(h);
                }
                let n0 = self.out.len();
                for &a in args.iter() {
                    self.expr(a);
                }
                self.expr(concl);
                push_cmd(&mut self.out, if shared { cmd::THM_SAVE } else { cmd::THM }, thm.0);
                if let Some(t) = &mut self.tally {
                    t.add(self.env, p, thm.0, self.out.len() - n0);
                }
            }
            Pf::Conv { target, from, cp } => {
                let n0 = self.out.len();
                self.expr(target);
                let n1 = self.out.len();
                self.proof(from);
                let n2 = self.out.len();
                push_cmd(&mut self.out, cmd::CONV, 0);
                self.cp(&cp);
                if shared {
                    push_cmd(&mut self.out, cmd::SAVE, 0);
                }
                if let Some(t) = &mut self.tally {
                    t.add(self.env, p, ByteCosts::CONV, n1 - n0 + self.out.len() - n2);
                }
            }
        }
        if shared {
            self.pheap.insert(p, self.next);
            self.next += 1;
        }
    }
}

/// Where a part of the file goes while statements are added.
enum Sink {
    Mem(Vec<u8>),
    File(std::io::BufWriter<std::fs::File>, std::path::PathBuf),
    /// Nothing is written (a census): only usage is counted.
    Discard,
}

/// A part of the file being written, and its length so far.
struct Part {
    sink: Sink,
    len: u64,
}

impl Part {
    fn new(sink: Sink) -> Part { Part { sink, len: 0 } }

    fn file(path: std::path::PathBuf) -> std::io::Result<Part> {
        let f = std::fs::File::create(&path)?;
        Ok(Part::new(Sink::File(std::io::BufWriter::with_capacity(1 << 20, f), path)))
    }

    fn emit(&mut self, bytes: &[u8]) -> std::io::Result<()> {
        use std::io::Write;
        self.len += bytes.len() as u64;
        match &mut self.sink {
            Sink::Mem(v) => v.extend_from_slice(bytes),
            Sink::File(f, _) => f.write_all(bytes)?,
            Sink::Discard => {}
        }
        Ok(())
    }

    fn align(&mut self) -> std::io::Result<()> {
        let pad = (8 - self.len % 8) % 8;
        self.emit(&[0; 8][..pad as usize])
    }

    /// Append the part to `o` and delete its file; or return its bytes if it is in memory.
    fn drain_into(self, o: &mut impl std::io::Write) -> std::io::Result<Vec<u8>> {
        match self.sink {
            Sink::Mem(v) => Ok(v),
            Sink::File(w, path) => {
                drop(w.into_inner().map_err(|e| e.into_error())?);
                std::io::copy(&mut std::fs::File::open(&path)?, o)?;
                std::fs::remove_file(&path)?;
                Ok(Vec::new())
            }
            Sink::Discard => Ok(Vec::new()),
        }
    }
}

/// An MMB file written while the environment grows. `flush` appends the proof-stream entries
/// and the term and theorem table data of the statements added since the last call, so their
/// proofs, and the expressions of statements nothing will use again, can then be freed;
/// `finish` writes the header, the tables, the stream and the index. The statements must not
/// change in between (tampering goes through `extra_hyps` and `tamper_concl`).
pub struct Writer {
    /// The proof stream.
    stream: Part,
    /// The data of the term and theorem tables (argument arrays and unify streams), each entry
    /// 8-aligned within the part.
    tables: Part,
    /// For each term: argument count, return sort and def flag, and its data's offset in `tables`.
    term_tab: Vec<(u16, u8, u64)>,
    /// For each theorem: argument count and its data's offset in `tables`.
    thm_tab: Vec<(u16, u64)>,
    /// The names of the index, each followed by a zero byte.
    names: Part,
    /// Each statement, its position in `stream` and its name's in `names`.
    stmt_pos: Vec<(Stmt, u64, u64)>,
    /// The next statement of `Env::order` to write.
    next: usize,
    /// For each theorem, how many distinct proof steps of the written proofs use it.
    pub usage: Vec<u32>,
    /// Axioms to write with an extra first hypothesis, and theorems to state with another
    /// conclusion (negative tests: the proofs stay as they are).
    pub extra_hyps: HashMap<String, E>,
    pub tamper_concl: HashMap<String, E>,
    /// If set, proof bytes are tallied here (and measured even when discarding).
    pub byte_costs: Option<ByteCosts>,
    /// Each sort's modifiers.
    sort_mods: Vec<u8>,
    /// Sharded generation: the declaration being flushed, whether this shard owns it, and the
    /// shard file that takes the statements instead of the parts.
    pub decl: u32,
    pub owned: bool,
    pub shard: Option<ShardOut>,
    /// Part mode (separate certificates): statements not owned are restated in this file,
    /// theorems as axioms (an earlier part proves them).
    pub restate: bool,
    /// The largest heap (arguments, hypotheses and saved steps) of a theorem written so far.
    pub max_heap: u32,
}

impl Writer {
    /// A writer that keeps the file in memory.
    pub fn in_memory() -> Writer {
        let mem = || Part::new(Sink::Mem(Vec::new()));
        Self::with(mem(), mem(), mem())
    }

    /// A writer that keeps the stream in the file `tmp`, and the table data and names next to
    /// it, until `finish`.
    pub fn to_file(tmp: &std::path::Path) -> std::io::Result<Writer> {
        let next_to = |ext: &str| {
            let mut p = tmp.as_os_str().to_owned();
            p.push(ext);
            std::path::PathBuf::from(p)
        };
        Ok(Self::with(Part::file(tmp.to_path_buf())?, Part::file(next_to(".tables"))?, Part::file(next_to(".names"))?))
    }

    /// A writer that only counts usage.
    pub fn discard() -> Writer {
        let none = || Part::new(Sink::Discard);
        Self::with(none(), none(), none())
    }

    fn with(stream: Part, tables: Part, names: Part) -> Writer {
        Writer {
            stream,
            tables,
            term_tab: Vec::new(),
            thm_tab: Vec::new(),
            names,
            stmt_pos: Vec::new(),
            next: 0,
            usage: Vec::new(),
            extra_hyps: HashMap::default(),
            tamper_concl: HashMap::default(),
            byte_costs: None,
            sort_mods: Vec::new(),
            decl: 0,
            owned: true,
            shard: None,
            restate: false,
            max_heap: 0,
        }
    }

    /// The size of the stream so far.
    pub fn stream_len(&self) -> u64 { self.stream.len }

    /// The bytes written so far: stream, table data and names.
    pub fn written(&self) -> u64 { self.stream.len + self.tables.len + self.names.len }

    /// Approximate heap bytes (for memory diagnostics).
    pub fn approx_bytes(&self) -> usize {
        self.stmt_pos.capacity() * 24 + self.term_tab.capacity() * 16 + self.thm_tab.capacity() * 16 + self.usage.capacity() * 4
    }

    /// Write the statements added since the last call. With `owned` false (sharded
    /// generation: a replayed declaration), only lemmas are written; the others are noted as
    /// references in the shard file.
    pub fn flush(&mut self, env: &Env) -> std::io::Result<()> {
        self.usage.resize(env.thms.len(), 0);
        while self.next < env.order.len() {
            let st = env.order[self.next];
            self.next += 1;
            let lemma = is_lemma(env, st);
            let restated = !self.owned && !lemma;
            if restated && !self.restate {
                if let Some(sh) = &mut self.shard {
                    sh.foreign(self.decl, st, stmt_name(env, st))?;
                }
                continue
            }
            if let Some(raw) = self.encode(env, st, restated)? {
                match &mut self.shard {
                    Some(sh) => sh.owned(self.decl, &raw)?,
                    None => self.push_raw(&raw)?,
                }
            }
        }
        Ok(())
    }

    /// A statement as it goes into the file, or `None` when discarding (usage and byte costs are
    /// still counted). `as_axiom`: a theorem is written as an axiom.
    fn encode(&mut self, env: &Env, st: Stmt, as_axiom: bool) -> std::io::Result<Option<Raw>> {
        let discard = matches!(self.stream.sink, Sink::Discard) && self.shard.is_none();
        let name = stmt_name(env, st).to_string();
        Ok(Some(match st {
            Stmt::Sort(s) => Raw { kind: st, cmd: cmd::ST_SORT, name, nargs: 0, flags: env.sorts[s as usize].mods, table: Vec::new(), body: Vec::new() },
            Stmt::Term(t) => {
                if discard {
                    return Ok(None)
                }
                let d = &env.terms[t.0 as usize];
                let body = match d.kind {
                    TermKind::Def { body, .. } => Some(body),
                    TermKind::Term => None,
                };
                let table = table_bytes(env, &d.args, Some(d.ret), body.as_slice(), &[]);
                let flags = d.ret | if body.is_some() { 0x80 } else { 0 };
                let nargs = u16::try_from(d.args.len()).unwrap();
                let (cmd, body) = match body {
                    None => (cmd::ST_TERM, Vec::new()),
                    Some(body) => {
                        let mut pr = Proof::new(env, d.args.len());
                        pr.count_e(body);
                        pr.expr(body);
                        pr.out.push(0);
                        (if d.local { cmd::ST_LOCAL_DEF } else { cmd::ST_TERM }, pr.out)
                    }
                };
                Raw { kind: st, cmd, name, nargs, flags, table, body }
            }
            Stmt::Thm(t) => {
                let d = &env.thms[t.0 as usize];
                let (axiom, proof) = if as_axiom { (true, None) } else { (d.axiom, d.proof) };
                let mut hyps = d.hyps.to_vec();
                if d.axiom {
                    if let Some(&h) = self.extra_hyps.get(&*d.name) {
                        hyps.insert(0, h);
                    }
                }
                let mut pr = Proof::new(env, d.args.len());
                for &h in &hyps {
                    pr.count_e(h);
                }
                match proof {
                    Some(p) => pr.count_p(p),
                    None => pr.count_e(d.concl),
                }
                for &p in pr.pcounts.keys() {
                    if let Pf::Thm { thm, .. } = env.pf(p) {
                        self.usage[thm.0 as usize] += 1;
                    }
                }
                if discard {
                    if let (Some(p), Some(bc)) = (proof, &mut self.byte_costs) {
                        for &h in &hyps {
                            pr.expr(h);
                            pr.hyps.push(pr.next);
                            pr.next += 1;
                        }
                        pr.tally = Some(bc);
                        pr.proof(p);
                    }
                    return Ok(None)
                }
                let concl = self.tamper_concl.get(&*d.name).copied().unwrap_or(d.concl);
                let table = table_bytes(env, &d.args, None, &[concl], &hyps);
                pr.tally = self.byte_costs.as_mut();
                for &h in &hyps {
                    pr.expr(h);
                    push_cmd(&mut pr.out, cmd::HYP, 0);
                    pr.hyps.push(pr.next);
                    pr.next += 1;
                }
                match proof {
                    Some(p) => pr.proof(p),
                    None => pr.expr(d.concl),
                }
                pr.out.push(0);
                self.max_heap = self.max_heap.max(pr.next);
                let cmd = if axiom {
                    cmd::ST_AXIOM
                } else if d.local {
                    cmd::ST_LOCAL_THM
                } else {
                    cmd::ST_THM
                };
                Raw { kind: st, cmd, name, nargs: u16::try_from(d.args.len()).unwrap(), flags: 0, table, body: pr.out }
            }
        }))
    }

    /// Append an encoded statement; it gets the next number of its kind.
    fn push_raw(&mut self, raw: &Raw) -> std::io::Result<()> {
        let st = match raw.kind {
            Stmt::Sort(_) => {
                self.sort_mods.push(raw.flags);
                Stmt::Sort(u8::try_from(self.sort_mods.len() - 1).unwrap())
            }
            Stmt::Term(_) => {
                self.tables.align()?;
                self.term_tab.push((raw.nargs, raw.flags, self.tables.len));
                self.tables.emit(&raw.table)?;
                Stmt::Term(TId(u32::try_from(self.term_tab.len() - 1).unwrap()))
            }
            Stmt::Thm(_) => {
                self.tables.align()?;
                self.thm_tab.push((raw.nargs, self.tables.len));
                self.tables.emit(&raw.table)?;
                Stmt::Thm(ThId(u32::try_from(self.thm_tab.len() - 1).unwrap()))
            }
        };
        // table entries point to their data in 32 bits: fail now rather than at `finish`
        let header = 48 + self.sort_mods.len() as u64 + 8 * (self.term_tab.len() + self.thm_tab.len()) as u64;
        if header + self.tables.len > u64::from(u32::MAX) {
            return Err(bad(format!("the MMB table data passed 4 GiB at statement {}: the format's table pointers are 32-bit", raw.name)))
        }
        self.stmt_pos.push((st, self.stream.len, self.names.len));
        self.names.emit(raw.name.as_bytes())?;
        self.names.emit(&[0])?;
        self.stream.emit(&stmt_header(raw.cmd, raw.body.len()))?;
        self.stream.emit(&raw.body)
    }

    /// Finish the file: flush, then the header and tables, the stream, and the index. Returns
    /// the file's contents for an in-memory writer, and writes `out` otherwise. The statements
    /// are not read again: `flush` took what the file needs.
    pub fn finish(mut self, env: &Env, out: Option<&std::path::Path>) -> std::io::Result<(u64, Vec<u8>)> {
        self.flush(env)?;
        self.finish_file(out)
    }

    /// `finish` without a last flush: everything the file needs is in the writer.
    fn finish_file(mut self, out: Option<&std::path::Path>) -> std::io::Result<(u64, Vec<u8>)> {
        self.stream.emit(&[0])?;
        let (nsorts, nterms, nthms) = (self.sort_mods.len(), self.term_tab.len(), self.thm_tab.len());

        // ---- header and table entries, then the table data (from `flush`). (`mmb.md`
        // describes a `p32` pointer to a unify stream instead of having it inline after the
        // argument array, but mm0-c, mm0b_parser and mm0-zig all read it inline.)
        let mut f: Vec<u8> = vec![0; 40 + nsorts];
        let align = |f: &mut Vec<u8>| {
            while f.len() % 8 != 0 {
                f.push(0)
            }
        };
        align(&mut f);
        let p_terms = f.len();
        f.resize(p_terms + 8 * nterms, 0);
        let p_thms = f.len();
        f.resize(p_thms + 8 * nthms, 0);
        align(&mut f);
        let base = f.len() as u64;
        let p32 = |at: u64| u32::try_from(base + at).expect("MMB tables over 4 GiB").to_le_bytes();
        for (i, &(nargs, flags, at)) in self.term_tab.iter().enumerate() {
            let e = p_terms + 8 * i;
            f[e..e + 2].copy_from_slice(&nargs.to_le_bytes());
            f[e + 2] = flags;
            f[e + 4..e + 8].copy_from_slice(&p32(at));
        }
        for (i, &(nargs, at)) in self.thm_tab.iter().enumerate() {
            let e = p_thms + 8 * i;
            f[e..e + 2].copy_from_slice(&nargs.to_le_bytes());
            f[e + 4..e + 8].copy_from_slice(&p32(at));
        }
        let p_proof = base + self.tables.len;
        let stream_len = self.stream.len;

        // ---- index with a Name table, after the stream and 8 zero bytes
        let mut x: Vec<u8> = vec![0; 8];
        let mut at = p_proof + stream_len + 8;
        while at % 8 != 0 {
            x.push(0);
            at += 1;
        }
        let p_index = at;
        x.extend(1u64.to_le_bytes());
        x.extend(b"Name");
        x.extend(0u32.to_le_bytes());
        let p_names = p_index + 24;
        x.extend(p_names.to_le_bytes());
        let nentries = nsorts + nterms + nthms;
        let table = x.len();
        x.resize(table + 16 * nentries, 0);
        let p_name0 = p_proof + stream_len + x.len() as u64;
        let entry_of = |st: Stmt| -> usize {
            match st {
                Stmt::Sort(s) => s as usize,
                Stmt::Term(t) => nsorts + t.0 as usize,
                Stmt::Thm(t) => nsorts + nterms + t.0 as usize,
            }
        };
        for &(st, pos, name) in &self.stmt_pos {
            let k = table + 16 * entry_of(st);
            x[k..k + 8].copy_from_slice(&(p_proof + pos).to_le_bytes());
            x[k + 8..k + 16].copy_from_slice(&(p_name0 + name).to_le_bytes());
        }
        let tail = [0u8; 8];

        f[0..4].copy_from_slice(b"MM0B");
        f[4] = 1;
        f[5] = u8::try_from(nsorts).unwrap();
        f[8..12].copy_from_slice(&u32::try_from(nterms).unwrap().to_le_bytes());
        f[12..16].copy_from_slice(&u32::try_from(nthms).unwrap().to_le_bytes());
        f[16..20].copy_from_slice(&(p_terms as u32).to_le_bytes());
        f[20..24].copy_from_slice(&(p_thms as u32).to_le_bytes());
        f[24..28].copy_from_slice(&u32::try_from(p_proof).unwrap().to_le_bytes());
        f[32..40].copy_from_slice(&p_index.to_le_bytes());
        for (i, &m) in self.sort_mods.iter().enumerate() {
            f[40 + i] = m;
        }
        let size = p_name0 + self.names.len + tail.len() as u64;
        match out {
            Some(path) if matches!(self.stream.sink, Sink::File(..)) => {
                use std::io::Write;
                let mut o = std::io::BufWriter::new(std::fs::File::create(path)?);
                o.write_all(&f)?;
                self.tables.drain_into(&mut o)?;
                self.stream.drain_into(&mut o)?;
                o.write_all(&x)?;
                self.names.drain_into(&mut o)?;
                o.write_all(&tail)?;
                o.flush()?;
                Ok((size, Vec::new()))
            }
            _ if matches!(self.stream.sink, Sink::Discard) => Ok((size, Vec::new())),
            _ => {
                let mut sink = std::io::sink();
                f.extend(self.tables.drain_into(&mut sink)?);
                f.extend(self.stream.drain_into(&mut sink)?);
                f.extend(x);
                f.extend(self.names.drain_into(&mut sink)?);
                f.extend(tail);
                Ok((size, f))
            }
        }
    }
}

/// Serialize the environment in one go.
pub fn write(env: &Env) -> Vec<u8> { Writer::in_memory().finish(env, None).unwrap().1 }

// ---------------------------------------------------------------------------- sharded output

fn bad(msg: String) -> std::io::Error { std::io::Error::other(msg) }

/// Copy a command stream (a unify stream or a proof stream, ending in a zero byte) from `src`,
/// renumbering the terms and theorems it names.
fn remap_stream(src: &[u8], terms: &[u32], thms: &[u32], out: &mut Vec<u8>) -> std::io::Result<usize> {
    let mut i = 0;
    loop {
        let Some(&c) = src.get(i) else { return Err(bad("unterminated command stream".into())) };
        i += 1;
        if c == 0 {
            out.push(0);
            return Ok(i)
        }
        let n = [0, 1, 2, 4][(c >> 6) as usize];
        let Some(b) = src.get(i..i + n) else { return Err(bad("truncated command".into())) };
        let data = b.iter().rev().fold(0u32, |a, &x| (a << 8) | u32::from(x));
        i += n;
        let op = c & 0x3F;
        let map = match op {
            cmd::TERM | cmd::TERM_SAVE | cmd::UTERM | cmd::UTERM_SAVE => Some(terms),
            cmd::THM | cmd::THM_SAVE => Some(thms),
            _ => None,
        };
        let data = match map {
            Some(m) => *m.get(data as usize).ok_or_else(|| bad(format!("statement {data} out of range")))?,
            None => data,
        };
        push_cmd(out, op, data);
    }
}

struct ShardReader {
    r: std::io::BufReader<std::fs::File>,
}

impl ShardReader {
    fn u8(&mut self) -> std::io::Result<Option<u8>> {
        use std::io::Read;
        let mut b = [0u8];
        match self.r.read(&mut b)? {
            0 => Ok(None),
            _ => Ok(Some(b[0])),
        }
    }

    fn exact<const N: usize>(&mut self) -> std::io::Result<[u8; N]> {
        use std::io::Read;
        let mut b = [0u8; N];
        self.r.read_exact(&mut b)?;
        Ok(b)
    }

    fn bytes(&mut self) -> std::io::Result<Vec<u8>> {
        use std::io::Read;
        let n = u32::from_le_bytes(self.exact()?) as usize;
        let mut v = vec![0; n];
        self.r.read_exact(&mut v)?;
        Ok(v)
    }
}

fn hash_bytes(seed: u8, nargs: u16, b: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::hash::DefaultHasher::new();
    (seed, nargs, b).hash(&mut h);
    h.finish()
}

/// Merge the files of a sharded generation into one MMB file `out` (built in temporary files
/// next to it). Shard `s` owns the declarations from `starts[s]` up to the next shard's start;
/// the shards are read in order, and each file is deleted once read.
///
/// Each shard numbers statements its own way, so terms and theorems are renumbered in every
/// table entry and proof. A reference to another shard's statement is resolved by its
/// declaration and its position among that declaration's statements other than lemmas, and
/// checked by kind and name. Local theorems with the same statement (lemmas that several
/// shards made, such as numeral facts) are written once, and the lemmas of shard `s > 0` are
/// renamed `NAME_s<s>` (no lemma name of shard 0 ends that way, so names stay unique).
/// Returns the file's size.
pub fn merge(shards: &[std::path::PathBuf], starts: &[u32], out: &std::path::Path) -> std::io::Result<u64> {
    let mut tmp = out.as_os_str().to_owned();
    tmp.push(".part");
    let mut w = Writer::to_file(std::path::Path::new(&tmp))?;
    // per declaration: its statements other than lemmas, as (kind, number, name hash)
    let mut owner: HashMap<u32, Vec<(u8, u32, u64)>> = HashMap::default();
    let mut lemmas: HashMap<(u64, u64), u32> = HashMap::default();
    for (s, path) in shards.iter().enumerate() {
        let mut r = ShardReader { r: std::io::BufReader::with_capacity(1 << 20, std::fs::File::open(path)?) };
        let (mut terms, mut thms): (Vec<u32>, Vec<u32>) = (Vec::new(), Vec::new());
        let (mut fdecl, mut fpos) = (u32::MAX, 0usize);
        while let Some(tag) = r.u8()? {
            let decl = u32::from_le_bytes(r.exact()?);
            let [kind] = r.exact()?;
            let name = String::from_utf8(r.bytes()?).map_err(|_| bad("statement name is not UTF-8".into()))?;
            let nh = hash_bytes(0, 0, name.as_bytes());
            if tag == 1 {
                if decl != fdecl {
                    (fdecl, fpos) = (decl, 0);
                }
                let o = starts.iter().rposition(|&lo| lo <= decl).unwrap_or(0);
                let Some(&(k, id, h)) = owner.get(&decl).and_then(|v| v.get(fpos)) else {
                    return Err(bad(format!("shard {s}: `{name}` (declaration {decl}) is not in shard {o}'s output (did that shard skip a declaration?)")))
                };
                if (k, h) != (kind, nh) {
                    return Err(bad(format!("shard {s}: `{name}` (declaration {decl}) does not match shard {o}'s statement there")))
                }
                fpos += 1;
                match kind {
                    1 => terms.push(id),
                    2 => thms.push(id),
                    _ => {}
                }
                continue
            }
            let [c] = r.exact()?;
            let nargs = u16::from_le_bytes(r.exact()?);
            let [flags] = r.exact()?;
            let (table0, body0) = (r.bytes()?, r.bytes()?);
            let lemma = kind == 2 && name.starts_with(crate::lean::FACT_PREFIX);
            let skip = 8 * (nargs as usize + usize::from(kind == 1));
            let mut table = table0.get(..skip).ok_or_else(|| bad("short table entry".into()))?.to_vec();
            if kind != 0 {
                remap_stream(&table0[skip..], &terms, &thms, &mut table)?;
            }
            let mut body = Vec::new();
            if !body0.is_empty() {
                remap_stream(&body0, &terms, &thms, &mut body)?;
            }
            let (st, id) = match kind {
                0 => (Stmt::Sort(0), w.sort_mods.len() as u32),
                1 => (Stmt::Term(TId(0)), w.term_tab.len() as u32),
                _ => (Stmt::Thm(ThId(0)), w.thm_tab.len() as u32),
            };
            if c == cmd::ST_LOCAL_THM {
                let key = (hash_bytes(1, nargs, &table), hash_bytes(2, nargs, &table));
                if let Some(&old) = lemmas.get(&key) {
                    thms.push(old);
                    if !lemma {
                        owner.entry(decl).or_default().push((kind, old, nh));
                    }
                    continue
                }
                lemmas.insert(key, id);
            }
            let name = if lemma && s > 0 { format!("{name}_s{s}") } else { name };
            w.push_raw(&Raw { kind: st, cmd: c, name, nargs, flags, table, body })?;
            match kind {
                1 => terms.push(id),
                2 => thms.push(id),
                _ => {}
            }
            if !lemma {
                owner.entry(decl).or_default().push((kind, id, nh));
            }
        }
        drop(r);
        std::fs::remove_file(path)?;
    }
    Ok(w.finish_file(Some(out))?.0)
}
