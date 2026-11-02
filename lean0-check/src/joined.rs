//! The text a verifier checks a certificate against (audit §7).
//!
//! A certificate's statement file (`NAME.mm0`, or `NAME.partK.mm0` for part `K` of a
//! multi-part certificate) is a two-line header (a doc comment and an `import`) followed by its
//! own statements. The certificate is checked against the spec, then the statements of the
//! earlier parts with each theorem stated as an axiom (an earlier part proves it) and each
//! abstract definition (a Lean theorem's proof term, whose body is only in that part's MMB) as
//! a plain term, then its own statements. This text is built here, from the statement files
//! alone, so the axioms a part assumes are exactly the theorems the earlier parts prove.

/// The statements of a statement file: everything after its two header lines.
fn own<'a>(name: &str, text: &'a str) -> Result<&'a str, String> {
    let header = |s: &'a str, what: &str, prefix: &str| -> Result<&'a str, String> {
        match s.split_once('\n') {
            Some((line, rest)) if line.starts_with(prefix) => Ok(rest),
            _ => Err(format!("{name}: expected the {what} line of lean0's header")),
        }
    };
    header(header(text, "first (`--|`)", "--|")?, "second (`import`)", "import ")
}

/// Restate a part's statements for a later part: `theorem` becomes `axiom`, and an abstract
/// `def` (a line `def ...;` without a body) becomes `term`.
fn restate(stmts: &str, out: &mut String) {
    for line in stmts.split_inclusive('\n') {
        let l = line.strip_suffix('\n').unwrap_or(line);
        if let Some(rest) = line.strip_prefix("theorem ") {
            out.push_str("axiom ");
            out.push_str(rest);
        } else if let Some(rest) = line.strip_prefix("def ").filter(|_| !l.contains('=') && l.ends_with(';')) {
            out.push_str("term ");
            out.push_str(rest);
        } else {
            out.push_str(line);
        }
    }
}

/// The text to check the certificate of the last of `files` (name, contents) against, the
/// others being the earlier parts in order.
pub fn joined(spec: &str, files: &[(String, String)]) -> Result<String, String> {
    let Some(((last_name, last), earlier)) = files.split_last() else { return Err("no statement files".into()) };
    let mut out = String::from(spec);
    for (name, text) in earlier {
        restate(own(name, text)?, &mut out);
    }
    out.push_str(own(last_name, last)?);
    Ok(out)
}
