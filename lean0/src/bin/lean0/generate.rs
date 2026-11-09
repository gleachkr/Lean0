//! `lean0 gen EXPORT.ndjson OUT_DIR NAME [OPTIONS]` (the options are below):
//! check a lean4export file with nanoda, then write `NAME.mm0` (statements, importing the
//! spec), `NAME.mmb` (proofs), `NAME.stats.tsv`, `NAME.usage.tsv` and the spec (`lean.mm0`)
//! into `OUT_DIR`. The verifiers check `NAME.mmb` against the text `lean0 joined NAME.mm0`
//! prints. The spec is the embedded one unless `--spec` names another (for development).
//!
//! `--keep-going` skips declarations that cannot be certified (and so everything that depends on
//! them) instead of stopping; the output then certifies only the rest, and the stats file says
//! why each skipped declaration failed.
//!
//! `--stats-only` writes only the stats and usage files: a census of a large module without
//! writing a certificate that may run to gigabytes. `--statements-only` writes the `.mm0` but
//! no `.mmb`: for a part whose certificate would pass the MMB format's 4 GiB of table data, so
//! that the later parts can still restate its statements (it is then not certified).
//!
//! `--jobs N` generates in parallel: N shards (processes) each certify a range of declarations,
//! replaying the statements of the ones before it, and the shards' files are merged into one
//! `NAME.mmb` (`mm0kit::mmb::merge`). `--balance STATS` divides the declarations by
//! the times in an earlier run's stats file (of the same export) instead of by count.
//! `--parts P` writes P separate certificates instead, `NAME.partK.{mm0,mmb}` (N at a time,
//! balanced by proof nodes), each restating the earlier parts' statements as axioms (audit §7).
//! With `--max-pending M`, no part is started while M finished parts' `.mmb` files are still in
//! `OUT_DIR`, waiting for a checker to delete them (`check-parts.sh --follow --delete`): that
//! bounds the disk a large certificate takes at once. `--shard LO HI` and `--part K` are the
//! per-shard modes these use.
//!
//! The tamper options are for negative tests. They change a statement in both the `.mm0` and
//! the `.mmb` but keep the proofs, so a verifier must reject the result exactly when some proof
//! relies on the original statement: `--tamper-axiom` adds the false premise `le (s nz) nz` to an
//! axiom, `--tamper-theorem` replaces a theorem's statement by `ty G (srt lz) (srt lz)`. Since
//! a tampered axiom may be one of the spec's, a tampered run also writes `NAME.joined.mm0`, the
//! whole tampered text to verify against.

use lean0::gen::{memory_mb, Gen};
use mm0kit::mmb::Writer;
use nanoda_lib::util::Config;
use std::path::Path;

/// `, peak memory N MB` when known.
fn peak() -> String { memory_mb("VmHWM").map(|m| format!(", peak memory {m} MB")).unwrap_or_default() }

/// The spec's text and file name: the embedded spec, or the file `--spec` names.
struct Spec {
    text: String,
    file: String,
    /// the `--spec` argument, for the shards
    path: Option<String>,
}

pub fn run(args: &[String]) -> Result<(), String> {
    let usage = "usage: lean0 gen EXPORT.ndjson OUT_DIR NAME [--keep-going] [--stats-only | --statements-only] [--jobs N [--parts P [--max-pending M]] [--balance STATS]] [--spec SPEC.mm0] [--tamper-axiom A | --tamper-theorem T]... [--unchecked]";
    let [export, out, name, opts @ ..] = args else { return Err(usage.into()) };
    let mut spec = Spec { text: lean0_check::SPEC.to_string(), file: "lean.mm0".into(), path: None };
    let mut tamper_axioms = Vec::new();
    let mut tamper_thms = Vec::new();
    let mut keep_going = false;
    let mut stats_only = false;
    let mut statements_only = false;
    let mut unchecked = false;
    let (mut jobs, mut balance, mut shard, mut parts, mut part, mut max_pending) = (None, None, None, None, None, None);
    let mut it = opts.iter();
    while let Some(o) = it.next() {
        if o == "--keep-going" {
            keep_going = true;
            continue
        }
        if o == "--stats-only" {
            stats_only = true;
            continue
        }
        if o == "--statements-only" {
            statements_only = true;
            continue
        }
        if o == "--unchecked" {
            unchecked = true;
            continue
        }
        match (o.as_str(), it.next()) {
            ("--tamper-axiom", Some(a)) => tamper_axioms.push(a.clone()),
            ("--tamper-theorem", Some(t)) => tamper_thms.push(t.clone()),
            ("--jobs", Some(n)) => jobs = Some(n.parse::<usize>().map_err(|_| usage.to_string())?.max(1)),
            ("--balance", Some(f)) => balance = Some(f.clone()),
            ("--spec", Some(f)) => {
                spec.text = std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?;
                spec.file = Path::new(f).file_name().map_or(f.clone(), |n| n.to_string_lossy().to_string());
                spec.path = Some(f.clone());
            }
            ("--parts", Some(n)) => parts = Some(n.parse::<usize>().map_err(|_| usage.to_string())?.max(1)),
            ("--max-pending", Some(n)) => max_pending = Some(n.parse::<usize>().map_err(|_| usage.to_string())?.max(1)),
            ("--part", Some(k)) => part = Some(k.parse::<usize>().map_err(|_| usage.to_string())?),
            ("--shard", Some(lo)) => {
                let hi = it.next().ok_or(usage)?;
                shard = Some((lo.parse::<usize>().map_err(|_| usage.to_string())?, hi.parse::<usize>().map_err(|_| usage.to_string())?));
            }
            _ => return Err(usage.into()),
        }
    }
    if max_pending.is_some() && (parts.is_none() || stats_only) {
        return Err("--max-pending needs --parts (and a certificate, not --stats-only)".into())
    }
    // the statements import the spec: a copy next to them (not in a shard's own directory)
    if shard.is_none() && !stats_only {
        std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
        let f = Path::new(out).join(&spec.file);
        std::fs::write(&f, &spec.text).map_err(|e| format!("{}: {e}", f.display()))?;
    }
    if jobs.is_some() || parts.is_some() {
        if statements_only {
            return Err("--statements-only is for one part (--shard LO HI --part K)".into())
        }
        if !tamper_axioms.is_empty() || !tamper_thms.is_empty() || unchecked {
            return Err("--jobs and --parts cannot be combined with tampering or --unchecked".into())
        }
        let jobs = jobs.unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()));
        return parallel([export, out, name], &spec, jobs, parts, max_pending, balance.as_deref(), keep_going, stats_only)
    }
    // part K of a multi-part certificate: its files are NAME.partK.*
    let base = name;
    let name = &match part {
        Some(k) => format!("{base}.part{k}"),
        None => base.clone(),
    };
    let cfg = serde_json::json!({
        "export_file_path": export,
        "unsafe_permit_all_axioms": true,
        "unpermitted_axiom_hard_error": false,
        "print_axioms": false,
        "nat_extension": true,
        "string_extension": true,
    });
    let cfg: Config = serde_json::from_value(cfg).map_err(|e| e.to_string())?;
    let (export_file, _) = cfg.to_export_file().map_err(|e| e.to_string())?;
    // The kernel decides; certificate generation only replays what it accepts. nanoda reports
    // a type error by panicking. `--unchecked` skips this, for the negative tests of the
    // inductive schema (declarations the kernel would reject, which the schema must reject
    // too): nanoda is not trusted, so a certificate made this way is as good as any other.
    if unchecked {
        eprintln!("lean0: --unchecked: the export is not checked by nanoda");
    } else {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| export_file.check_all_declars()))
            .map_err(|_| "nanoda rejected the export (see the panic message above)".to_string())?;
        eprintln!("nanoda: checked {} declarations{}", export_file.declars.len(), peak());
    }

    let mut gen = Gen::new(&spec.text)?;
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    // The file is written while generating, so tampered statements must be known now; the
    // statements themselves are changed after generation (for the `.mm0`).
    let mmb_path = out.join(format!("{name}.mmb"));
    let tmp = out.join(format!("{name}.mmb.part"));
    let mut writer = if stats_only || statements_only || (shard.is_some() && part.is_none()) {
        Writer::discard()
    } else {
        Writer::to_file(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?
    };
    gen.shard = shard;
    gen.parts = part.is_some();
    writer.restate = part.is_some();
    let shard_path = out.join(format!("{name}.shard"));
    if shard.is_some() && part.is_none() && !stats_only {
        writer.shard = Some(mm0kit::mmb::ShardOut::create(&shard_path).map_err(|e| format!("{}: {e}", shard_path.display()))?);
    }
    // the last shard has every public statement, and writes the `.mm0`
    let last_shard = part.is_some() || shard.is_none_or(|(_, hi)| hi >= export_file.declars.len());
    if gen.costs.is_some() {
        writer.byte_costs = Some(mm0kit::mmb::ByteCosts { spec_thms: gen.spec_thms as u32, ..Default::default() });
    }
    let false_hyp = {
        let z = gen.env.app_n("nz", &[]);
        let sz = gen.env.app_n("s", &[z]);
        gen.env.app_n("le", &[sz, z])
    };
    let false_concl = {
        let (g, z) = (gen.env.var(0), gen.env.app_n("lz", &[]));
        let p = gen.env.app_n("srt", &[z]);
        gen.env.app_n("ty", &[g, p, p])
    };
    for a in &tamper_axioms {
        writer.extra_hyps.insert(a.clone(), false_hyp);
    }
    for t in &tamper_thms {
        writer.tamper_concl.insert(t.clone(), false_concl);
    }
    let start = std::time::Instant::now();
    let r = gen.run(&export_file, keep_going, &mut writer);
    let elapsed = start.elapsed();

    let mut stats = String::from("name\tkind\tok\tproof_nodes\ttype_mismatches\tmicros\tmessage\n");
    for s in &gen.stats {
        stats.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\n", s.name, s.kind, s.ok, s.proof_nodes, s.type_mismatches, s.micros, s.message.replace('\n', " ")));
    }
    std::fs::write(out.join(format!("{name}.stats.tsv")), stats).map_err(|e| e.to_string())?;
    if let Some(c) = &gen.costs {
        eprint!("{}", c.report(gen.stats.iter().map(|s| s.proof_nodes as u64).sum()));
        eprint!("{}", lean0::costs::rule_report(&gen.env, gen.spec_thms));
        if let Some(bc) = &writer.byte_costs {
            eprint!("{}", c.byte_report(&gen.env, bc));
        }
    }
    if let Err(e) = r {
        let _ = std::fs::remove_file(&tmp);
        return Err(e)
    }

    // local lemmas are not kept by name (`Env::forget_local_names`): one line for all of them
    let mut usage = String::from("statement\tkind\tuses\n");
    writer.flush(&gen.env).map_err(|e| e.to_string())?;
    let mut local = 0u64;
    for (t, &n) in gen.env.thms.iter().zip(&writer.usage) {
        if t.local {
            local += u64::from(n);
            continue
        }
        let kind = if t.axiom { "axiom" } else { "theorem" };
        usage.push_str(&format!("{}\t{kind}\t{n}\n", t.name));
    }
    usage.push_str(&format!("(local lemmas)\tlocal\t{local}\n"));
    std::fs::write(out.join(format!("{name}.usage.tsv")), usage).map_err(|e| e.to_string())?;
    if stats_only {
        eprintln!("lean0: {} declarations ({} skipped), {:.1} ms (stats only){}", gen.stats.len(),
            gen.stats.iter().filter(|s| !s.ok).count(), elapsed.as_secs_f64() * 1000.0, peak());
        return Ok(())
    }
    for a in &tamper_axioms {
        let Some(&t) = gen.env.thm_names.get(a) else { return Err(format!("no axiom {a}")) };
        let d = &mut gen.env.thms[t.0 as usize];
        if !d.axiom {
            return Err(format!("{a} is not an axiom"))
        }
        d.hyps = std::iter::once(false_hyp).chain(d.hyps.iter().copied()).collect();
    }
    for t in &tamper_thms {
        let Some(&id) = gen.env.thm_names.get(t) else { return Err(format!("no theorem {t}")) };
        let d = &mut gen.env.thms[id.0 as usize];
        if d.axiom {
            return Err(format!("{t} is not a theorem"))
        }
        d.concl = false_concl;
    }
    if !last_shard {
        if let Some(sh) = writer.shard.take() {
            sh.finish().map_err(|e| format!("{}: {e}", shard_path.display()))?;
        }
        eprintln!("lean0: shard of {} declarations, {:.1} ms{}", gen.stats.len(), elapsed.as_secs_f64() * 1000.0, peak());
        return Ok(())
    }
    let generated = gen.generated_text();
    let export_name = Path::new(export).file_name().unwrap().to_string_lossy().to_string();
    // a part's statements follow the earlier parts' (which `lean0 joined` restates as axioms)
    let import = match part {
        Some(k @ 1..) => format!("{base}.part{}.mm0", k - 1),
        _ => spec.file.clone(),
    };
    let header = format!("--| Generated by lean0 from `{export_name}`. Statements only; proofs are in `{name}.mmb`.\nimport \"{import}\";\n");
    std::fs::write(out.join(format!("{name}.mm0")), format!("{header}{generated}")).map_err(|e| e.to_string())?;
    // After tampering, the spec part may have changed too: print everything from the environment.
    if !tamper_axioms.is_empty() || !tamper_thms.is_empty() {
        let mut t = String::from("delimiter $ ( ) $;\n");
        for &st in &gen.env.order {
            if let Some(x) = gen.env.stmt_text(st) {
                t.push_str(&x);
            }
        }
        std::fs::write(out.join(format!("{name}.joined.mm0")), t).map_err(|e| e.to_string())?;
    }
    if let Some(sh) = writer.shard.take() {
        sh.finish().map_err(|e| format!("{}: {e}", shard_path.display()))?;
        eprintln!("lean0: shard of {} declarations, {:.1} ms{}", gen.stats.len(), elapsed.as_secs_f64() * 1000.0, peak());
        return Ok(())
    }
    if statements_only {
        eprintln!("lean0: {} declarations, statements only (no certificate){}", gen.stats.len(), peak());
        return Ok(())
    }
    let max_heap = writer.max_heap;
    let (size, _) = writer.finish(&gen.env, Some(&mmb_path)).map_err(|e| format!("{}: {e}", mmb_path.display()))?;
    let failed = gen.stats.iter().filter(|s| !s.ok).count();
    if size > u32::MAX as u64 {
        eprintln!("lean0: warning: the MMB file exceeds 4 GiB; mm0-zig keeps proof positions in 32 bits and will reject it");
    }
    if part.is_some() {
        eprintln!("lean0: {} bytes restate the earlier parts", gen.replayed_bytes);
    }
    eprintln!("lean0: {} theorems, largest heap {max_heap}", gen.env.thms.len());
    eprintln!(
        "lean0: {} declarations ({failed} skipped), {} MM0 statements, {} bytes of MMB, {:.1} ms{}",
        gen.stats.len(),
        gen.num_generated(),
        size,
        elapsed.as_secs_f64() * 1000.0,
        peak()
    );
    Ok(())
}

/// `--jobs N`: run N shards of `lean0` (this executable, `--shard`) over consecutive ranges of
/// declarations, then merge their files into one certificate and join their stats and usage.
/// With `--parts P`, run P shards (N at a time) and keep each as a certificate of its own,
/// `NAME.partK.{mm0,mmb}` (`--part K`), starting none while `max_pending` finished parts' `.mmb`
/// files are still in OUT. `files` is `[EXPORT, OUT, NAME]`.
fn parallel(files: [&String; 3], spec: &Spec, jobs: usize, parts: Option<usize>, max_pending: Option<usize>, balance: Option<&str>, keep_going: bool, stats_only: bool) -> Result<(), String> {
    let n = parts.unwrap_or(jobs);
    let [export, out, name] = files;
    let start = std::time::Instant::now();
    let cfg = serde_json::json!({ "export_file_path": export, "unsafe_permit_all_axioms": true, "nat_extension": true, "string_extension": true });
    let cfg: Config = serde_json::from_value(cfg).map_err(|e| e.to_string())?;
    let total = cfg.to_export_file().map_err(|e| e.to_string())?.0.declars.len();
    // weights from an earlier run (one stats line per declaration, in order), else 1 each: its
    // times, or for parts (whose size is the limit) its proof nodes
    let mut w = vec![1u64; total];
    if let Some(f) = balance {
        let text = std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?;
        let col = if parts.is_some() { 3 } else { 5 };
        let times: Vec<u64> = text.lines().skip(1).map(|l| l.split('\t').nth(col).and_then(|t| t.parse().ok()).unwrap_or(0)).collect();
        if times.len() == total {
            w = times.iter().map(|&t| t.max(1)).collect();
        } else {
            eprintln!("lean0: {f} has {} declarations, the export {total}: dividing by count", times.len());
        }
    }
    let sum: u64 = w.iter().sum();
    let mut starts = vec![0usize];
    let mut acc = 0u64;
    for (i, &x) in w.iter().enumerate() {
        if acc * n as u64 >= sum * starts.len() as u64 && starts.len() < n && i > *starts.last().unwrap() {
            starts.push(i);
        }
        acc += x;
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let dir = |k: usize| out.join(format!("{name}.shard{k}"));
    // the shard's own file names
    let sname = |k: usize| if parts.is_some() { format!("{name}.part{k}") } else { name.clone() };
    let spawn = |k: usize| -> Result<std::process::Child, String> {
        let (lo, hi) = (starts[k], starts.get(k + 1).copied().unwrap_or(total));
        std::fs::create_dir_all(dir(k)).map_err(|e| e.to_string())?;
        let log = std::fs::File::create(dir(k).join("log")).map_err(|e| e.to_string())?;
        let mut c = std::process::Command::new(&exe);
        c.args(["gen", export]).arg(dir(k)).arg(name).args(["--shard", &lo.to_string(), &hi.to_string()]);
        if let Some(f) = &spec.path {
            c.args(["--spec", f]);
        }
        if parts.is_some() {
            c.args(["--part", &k.to_string()]);
        }
        if keep_going {
            c.arg("--keep-going");
        }
        if stats_only {
            c.arg("--stats-only");
        }
        c.stderr(log).spawn().map_err(|e| e.to_string())
    };
    eprintln!("lean0: {} shards, {jobs} at a time, starting at declarations {starts:?} of {total}", starts.len());
    let mut pending: std::collections::VecDeque<usize> = (0..starts.len()).collect();
    let (mut running, mut failed) = (Vec::new(), Vec::new());
    // Parts are moved to OUT as each finishes (the `.mmb` last), so `check-parts.sh --follow`
    // can verify and delete them while the rest are made; `NAME.parts` says how many to expect,
    // and `NAME.partK.failed` that one will not come.
    let mut sizes = vec![0u64; starts.len()];
    let finish_part = |k: usize, ok: bool, sizes: &mut Vec<u64>| -> Result<(), String> {
        if parts.is_none() || stats_only {
            return Ok(())
        }
        if !ok {
            return std::fs::write(out.join(format!("{}.failed", sname(k))), "").map_err(|e| e.to_string())
        }
        for ext in ["mm0", "mmb"] {
            let f = format!("{}.{ext}", sname(k));
            std::fs::rename(dir(k).join(&f), out.join(&f)).map_err(|e| format!("{f}: {e}"))?;
        }
        sizes[k] = std::fs::metadata(out.join(format!("{}.mmb", sname(k)))).map_err(|e| e.to_string())?.len();
        Ok(())
    };
    if parts.is_some() && !stats_only {
        std::fs::write(out.join(format!("{name}.parts")), format!("{}\n", starts.len())).map_err(|e| e.to_string())?;
    }
    // finished parts whose `.mmb` is still in OUT (not yet checked and deleted)
    let waiting = || (0..starts.len()).filter(|&k| out.join(format!("{}.mmb", sname(k))).exists()).count();
    let mut held = false;
    while !pending.is_empty() || !running.is_empty() {
        while running.len() < jobs && !pending.is_empty() {
            if max_pending.is_some_and(|m| waiting() >= m) {
                if !held {
                    eprintln!("lean0: holding the next part until a checker deletes one of the {} waiting (--max-pending)", waiting());
                }
                held = true;
                break
            }
            held = false;
            let k = pending.pop_front().unwrap();
            running.push((k, spawn(k)?));
        }
        let before = running.len();
        let mut i = 0;
        while i < running.len() {
            match running[i].1.try_wait().map_err(|e| e.to_string())? {
                Some(st) => {
                    let k = running[i].0;
                    if !st.success() {
                        failed.push(k);
                    }
                    finish_part(k, st.success(), &mut sizes)?;
                    running.swap_remove(i);
                }
                None => i += 1,
            }
        }
        if running.len() == before {
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
    }
    failed.sort();
    let log_tail = |k: usize| {
        let t = std::fs::read_to_string(dir(k).join("log")).unwrap_or_default();
        t.lines().rev().take(3).collect::<Vec<_>>().into_iter().rev().collect::<Vec<_>>().join("\n")
    };
    if let Some(&k) = failed.first() {
        return Err(format!("shard {k} failed (log: {}):\n{}", dir(k).join("log").display(), log_tail(k)))
    }
    // stats in order; usage summed by statement (local lemmas are one line)
    let mut stats = String::new();
    let mut usage: Vec<(String, String, u64)> = Vec::new();
    let mut at: std::collections::HashMap<String, usize> = Default::default();
    let mut peak_mb = 0u64;
    for k in 0..starts.len() {
        let st = std::fs::read_to_string(dir(k).join(format!("{}.stats.tsv", sname(k)))).map_err(|e| e.to_string())?;
        let mut lines = st.lines();
        let head = lines.next().unwrap_or_default();
        if k == 0 {
            stats.push_str(head);
            stats.push('\n');
        }
        lines.for_each(|l| {
            stats.push_str(l);
            stats.push('\n');
        });
        let us = std::fs::read_to_string(dir(k).join(format!("{}.usage.tsv", sname(k)))).map_err(|e| e.to_string())?;
        for l in us.lines().skip(1) {
            let mut f = l.split('\t');
            let (Some(stmt), Some(kind), Some(n)) = (f.next(), f.next(), f.next().and_then(|n| n.parse::<u64>().ok())) else { continue };
            match at.get(stmt) {
                Some(&i) => usage[i].2 += n,
                None => {
                    at.insert(stmt.to_string(), usage.len());
                    usage.push((stmt.to_string(), kind.to_string(), n));
                }
            }
        }
        let log = std::fs::read_to_string(dir(k).join("log")).unwrap_or_default();
        if let Some(m) = log.lines().rev().find_map(|l| l.rsplit_once("peak memory ").and_then(|(_, m)| m.trim_end_matches(" MB").parse::<u64>().ok())) {
            peak_mb = peak_mb.max(m);
        }
    }
    std::fs::write(out.join(format!("{name}.stats.tsv")), &stats).map_err(|e| e.to_string())?;
    let mut u = String::from("statement\tkind\tuses\n");
    for (s, k, n) in &usage {
        u.push_str(&format!("{s}\t{k}\t{n}\n"));
    }
    std::fs::write(out.join(format!("{name}.usage.tsv")), u).map_err(|e| e.to_string())?;
    let ndecl = stats.lines().count() - 1;
    let skipped = stats.lines().skip(1).filter(|l| l.split('\t').nth(2) == Some("false")).count();
    let mut size = String::new();
    if !stats_only && parts.is_some() {
        if skipped > 0 {
            eprintln!("lean0: warning: {skipped} declarations were skipped; later parts replayed them, so their statements may not line up");
        }
        size = format!(", {} parts of {} bytes of MMB in all (largest {})", sizes.len(), sizes.iter().sum::<u64>(), sizes.iter().max().unwrap());
    } else if !stats_only {
        if skipped > 0 {
            eprintln!("lean0: warning: {skipped} declarations were skipped; later shards replayed them, so the merge may not line up");
        }
        let last = dir(starts.len() - 1);
        std::fs::rename(last.join(format!("{name}.mm0")), out.join(format!("{name}.mm0"))).map_err(|e| e.to_string())?;
        let files: Vec<_> = (0..starts.len()).map(|k| dir(k).join(format!("{name}.shard"))).collect();
        let starts32: Vec<u32> = starts.iter().map(|&s| s as u32).collect();
        let mmb = out.join(format!("{name}.mmb"));
        let bytes = mm0kit::mmb::merge(&files, &starts32, &mmb).map_err(|e| format!("merging the shards: {e}"))?;
        size = format!(", {bytes} bytes of MMB");
    }
    // keep each shard's log (its progress lines and cost reports go there)
    for k in 0..starts.len() {
        let _ = std::fs::rename(dir(k).join("log"), out.join(format!("{name}.shard{k}.log")));
        let _ = std::fs::remove_dir_all(dir(k));
    }
    eprintln!("lean0: {ndecl} declarations ({skipped} skipped) in {} shards{size}, {:.1} ms{}, peak memory per shard {peak_mb} MB",
        starts.len(), start.elapsed().as_secs_f64() * 1000.0, if stats_only { " (stats only)" } else { "" });
    Ok(())
}
