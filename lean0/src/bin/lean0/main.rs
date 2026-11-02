//! `lean0`: certificates for Lean 4 environments as Metamath Zero proofs.
//!
//! - `lean0 gen EXPORT.ndjson OUT_DIR NAME [...]`: make the certificate, `NAME.mm0` (the
//!   statements) and `NAME.mmb` (the proofs), or several parts (`generate.rs`).
//! - `lean0 joined STATEMENTS.mm0...`: print the text a verifier checks the certificate of the
//!   last file against (the earlier files being the earlier parts, in order), e.g.
//!   `lean0 joined x.mm0 > x.joined.mm0 && mm0-c x.mmb < x.joined.mm0`.
//! - `lean0 check EXPORT.ndjson STATEMENTS.mm0...`: check that the statements (of all parts, in
//!   order) say what the export's declarations say.
//! - `lean0 spec`: print the embedded spec.
//!
//! `joined`, `check` and `spec` are the trusted side, from the `lean0-check` crate, which does
//! not depend on the generator.

mod generate;

const USAGE: &str = "usage: lean0 gen EXPORT.ndjson OUT_DIR NAME [OPTIONS]
       lean0 joined [--spec SPEC.mm0] STATEMENTS.mm0...
       lean0 check EXPORT.ndjson STATEMENTS.mm0...
       lean0 spec";

/// The command's result: `Ok(false)` for a check that found problems (exit code 1), `Err` for
/// an error (exit code 1, or 2 for `check`).
fn run(args: &[String]) -> Result<bool, String> {
    match args {
        [cmd, rest @ ..] if cmd == "gen" => generate::run(rest).map(|()| true),
        [cmd, rest @ ..] if cmd == "joined" => {
            let (spec, files) = match rest {
                [o, f, files @ ..] if o == "--spec" => (std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?, files),
                files => (lean0_check::SPEC.to_string(), files),
            };
            let texts = files.iter().map(|f| Ok((f.clone(), std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?)))
                .collect::<Result<Vec<_>, String>>()?;
            print!("{}", lean0_check::joined::joined(&spec, &texts)?);
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
            print!("{}", lean0_check::SPEC);
            Ok(true)
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
