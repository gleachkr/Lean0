//! `lean0`: certificates for Lean 4 environments as Metamath Zero proofs.
//!
//! - `lean0 gen EXPORT.ndjson OUT_DIR NAME [...]`: make the certificate, `NAME.mm0` (the
//!   statements) and `NAME.mmb` (the proofs), or several parts (`generate.rs`).
//! - `lean0 joined STATEMENTS.mm0...`: print the text a verifier checks the certificate of the
//!   last file against (the earlier files being the earlier parts, in order), e.g.
//!   `lean0 joined x.mm0 > x.joined.mm0 && mm0-c x.mmb < x.joined.mm0`. With `--tg`, the
//!   embedded TG library takes the spec's place (for a certificate made by `tg-link`).
//! - `lean0 tg-link CERT.mmb LIB.mmb OUT.mmb`: TG mode (audit §11): write the certificate
//!   `CERT.mmb` (made against the spec) again as `OUT.mmb`, after the TG library's MMB file
//!   `LIB.mmb` (`scripts/tg-check.sh` makes it), with the spec's statements taken from the
//!   library, each checked to be the same statement there (`mm0kit::mmb::link`). Verify it
//!   against `lean0 joined --tg`.
//! - `lean0 check EXPORT.ndjson STATEMENTS.mm0...`: check that the statements (of all parts, in
//!   order) say what the export's declarations say.
//! - `lean0 spec [--tg]`: print the embedded spec (or the TG library's text).
//! - `lean0 modes [SPEC.mm0]`: check that the spec's relations are the functions and
//!   predicates they are read as (`mm0kit::modes`), and print the table.
//!
//! `joined`, `check` and `spec` are the trusted side, from the `lean0-check` crate, which does
//! not depend on the generator.

mod generate;

const USAGE: &str = "usage: lean0 gen EXPORT.ndjson OUT_DIR NAME [OPTIONS]
       lean0 joined [--spec SPEC.mm0 | --tg] STATEMENTS.mm0...
       lean0 tg-link CERT.mmb LIB.mmb OUT.mmb
       lean0 check EXPORT.ndjson STATEMENTS.mm0...
       lean0 spec [--tg]
       lean0 modes [SPEC.mm0]";

/// The command's result: `Ok(false)` for a check that found problems (exit code 1), `Err` for
/// an error (exit code 1, or 2 for `check`).
fn run(args: &[String]) -> Result<bool, String> {
    match args {
        [cmd, rest @ ..] if cmd == "gen" => generate::run(rest).map(|()| true),
        [cmd, rest @ ..] if cmd == "joined" => {
            let (spec, files) = match rest {
                [o, f, files @ ..] if o == "--spec" => (std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?, files),
                [o, files @ ..] if o == "--tg" => (lean0_check::tg::text()?, files),
                files => (lean0_check::spec().to_string(), files),
            };
            let texts = files.iter().map(|f| Ok((f.clone(), std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?)))
                .collect::<Result<Vec<_>, String>>()?;
            print!("{}", lean0_check::joined::joined(&spec, &texts)?);
            Ok(true)
        }
        [cmd, cert, lib, out] if cmd == "tg-link" => {
            let mut env = mm0kit::env::Env::new();
            mm0kit::parse::parse_into(&mut env, lean0_check::spec()).map_err(|e| format!("spec: {}", e.0))?;
            let l = mm0kit::mmb::link(cert.as_ref(), lib.as_ref(), out.as_ref(), env.order.len()).map_err(|e| e.to_string())?;
            eprintln!("tg-link: {out}: the library's {} statements, then the certificate's {} ({} bytes); the spec's {} are the library's",
                l.library, l.own, l.size, l.spec);
            Ok(true)
        }
        [cmd, export, files @ ..] if cmd == "check" && !files.is_empty() => {
            let c = lean0_check::check(export, files)?;
            for p in &c.report.problems {
                println!("{p}");
            }
            // what a person wants to read (the counts stay the last line, for scripts)
            const SHOWN: usize = 20;
            println!("Top-level declarations (nothing else in the export mentions them):");
            for d in c.top_level.iter().take(SHOWN) {
                println!("  {}", d.replace('\n', "\n    "));
            }
            if c.top_level.len() > SHOWN {
                println!("  ... and {} more", c.top_level.len() - SHOWN);
            }
            println!("lean0 check: {} declarations, {} statements, {} problems", c.report.checked, c.statements, c.report.problems.len());
            Ok(c.report.problems.is_empty())
        }
        [cmd] if cmd == "spec" => {
            print!("{}", lean0_check::spec());
            Ok(true)
        }
        [cmd, o] if cmd == "spec" && o == "--tg" => {
            print!("{}", lean0_check::tg::text()?);
            Ok(true)
        }
        [cmd, rest @ ..] if cmd == "modes" && rest.len() <= 1 => {
            let spec = match rest {
                [f] => std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?,
                _ => lean0_check::spec().to_string(),
            };
            let r = mm0kit::modes::check(&spec).map_err(|e| e.0)?;
            print!("{}", r.text);
            for e in &r.errors {
                println!("error: {e}");
            }
            Ok(r.errors.is_empty())
        }
        _ => Err(USAGE.into()),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.first().is_some_and(|c| c == "check");
    let child = std::thread::Builder::new().stack_size(256 << 20).spawn(move || run(&args)).unwrap();
    match child.join().unwrap_or_else(|_| Err("internal error (panic)".into())) {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("lean0: {e}");
            std::process::exit(if check { 2 } else { 1 });
        }
    }
}
