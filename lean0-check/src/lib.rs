//! The trusted side of Lean0, apart from the MM0 verifiers: what a certificate is checked
//! against, and whether its statements say what the Lean export says.
//!
//! - [`SPEC`]: the spec, `spec/lean.mm0`, embedded.
//! - [`joined`]: the text a verifier checks a certificate (or one part of a multi-part
//!   certificate) against: the spec, the earlier parts' statements restated, and the
//!   certificate's own statements (audit §7).
//! - [`statements`]: the statement checker (audit §8), and [`summary`]: the export's
//!   top-level declarations in Lean syntax, for the person reading the result.
//!
//! This crate is deliberately independent of the generator (the `lean0` crate and mm0kit): it
//! uses only nanoda's export parser and expressions, and reads the generated `.mm0` text
//! itself.

pub mod joined;
pub mod statements;
pub mod summary;

/// The trusted spec of LeanTT that every certificate is checked against.
pub const SPEC: &str = include_str!("../../spec/lean.mm0");

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
    let mut stmts = Vec::new();
    for f in files {
        let text = std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?;
        stmts.extend(statements::parse_mm0(&text).map_err(|e| format!("{f}: {e}"))?);
    }
    let cfg = serde_json::json!({ "export_file_path": export, "unsafe_permit_all_axioms": true, "nat_extension": true, "string_extension": true });
    let cfg: nanoda_lib::util::Config = serde_json::from_value(cfg).map_err(|e| e.to_string())?;
    let (export_file, _) = cfg.to_export_file().map_err(|e| e.to_string())?;
    let report = statements::check(&export_file, &stmts);
    Ok(Checked { report, statements: stmts.len(), top_level: summary::top_level(&export_file) })
}
