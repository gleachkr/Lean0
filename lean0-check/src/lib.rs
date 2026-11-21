//! The trusted side of Lean0, apart from the MM0 verifiers: what a certificate is checked
//! against, and whether its statements say what the Lean export says.
//!
//! - [`spec`]: the spec, `spec/lean.mm0` with the four files it imports, embedded.
//! - [`joined`]: the text a verifier checks a certificate (or one part of a multi-part
//!   certificate) against: the spec, the earlier parts' statements restated, and the
//!   certificate's own statements (audit §7).
//! - [`tg`]: the TG library, embedded: in TG mode the text a certificate is checked against
//!   in place of the spec (audit §11).
//! - [`statements`]: the statement checker (audit §8), and [`summary`]: the export's
//!   top-level declarations in Lean syntax, for the person reading the result.
//!
//! This crate is deliberately independent of the generator (the `lean0` crate and mm0kit): it
//! uses only nanoda's export parser and expressions, and reads the generated `.mm0` text
//! itself.

pub mod joined;
pub mod statements;
pub mod summary;
pub mod tg;

/// The spec's files, by name: `lean.mm0` imports the others.
const SPEC_FILES: &[(&str, &str)] = &[
    ("lean-core.mm0", include_str!("../../spec/lean-core.mm0")),
    ("lean-ind.mm0", include_str!("../../spec/lean-ind.mm0")),
    ("lean-quot.mm0", include_str!("../../spec/lean-quot.mm0")),
    ("lean-lit.mm0", include_str!("../../spec/lean-lit.mm0")),
    ("lean.mm0", include_str!("../../spec/lean.mm0")),
];

/// The trusted spec of LeanTT that every certificate is checked against: `spec/lean.mm0`
/// with the files it imports, as one text (core, inductive types, quotients, literals).
pub fn spec() -> &'static str {
    static SPEC: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    SPEC.get_or_init(|| flatten(SPEC_FILES, "lean.mm0").expect("the embedded spec's imports"))
}

/// The text of the file `top` of `files` with each `import "F";` line replaced by the text
/// of `F` (itself flattened, and only the first time: as `abc join` does, so the declarations
/// come in the order an MMB file compiled from `top` has them).
pub fn flatten(files: &[(&str, &str)], top: &str) -> Result<String, String> {
    fn go(files: &[(&str, &str)], name: &str, seen: &mut Vec<String>, out: &mut String) -> Result<(), String> {
        if seen.iter().any(|s| s == name) {
            return Ok(())
        }
        seen.push(name.to_string());
        let Some(&(_, src)) = files.iter().find(|f| f.0 == name) else { return Err(format!("no embedded file {name}")) };
        for line in src.split_inclusive('\n') {
            if line.starts_with("import") {
                let Some(file) = line.trim_end().strip_prefix("import \"").and_then(|l| l.strip_suffix("\";")) else {
                    return Err(format!("{name}: unexpected import line {line:?}"))
                };
                go(files, file, seen, out)?;
            } else {
                out.push_str(line);
            }
        }
        if !out.ends_with('\n') {
            out.push('\n');
        }
        Ok(())
    }
    let mut out = String::new();
    go(files, top, &mut Vec::new(), &mut out)?;
    Ok(out)
}

/// What `lean0 check` found.
pub struct Checked {
    pub report: statements::Report,
    /// how many statements the files have
    pub statements: usize,
    /// the export's top-level declarations, in Lean syntax ([`summary`])
    pub top_level: Vec<String>,
}

/// Check that the statement files (all parts of a certificate, in order) say what the export's
/// declarations say.
pub fn check(export: &str, files: &[String]) -> Result<Checked, String> {
    let mut stmts = statements::spec_statements(spec())?;
    let nspec = stmts.len();
    for f in files {
        let text = std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?;
        stmts.extend(statements::parse_mm0(&text).map_err(|e| format!("{f}: {e}"))?);
    }
    let cfg = serde_json::json!({ "export_file_path": export, "unsafe_permit_all_axioms": true, "nat_extension": true, "string_extension": true });
    let cfg: nanoda_lib::util::Config = serde_json::from_value(cfg).map_err(|e| e.to_string())?;
    let (export_file, _) = cfg.to_export_file().map_err(|e| e.to_string())?;
    let report = statements::check(&export_file, &stmts);
    Ok(Checked { report, statements: stmts.len() - nspec, top_level: summary::top_level(&export_file) })
}
