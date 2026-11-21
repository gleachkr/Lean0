//! The TG library (`spec/tg`), embedded: in TG mode a certificate is verified against this
//! text instead of the spec (audit §11). Its top file, `lean-tg-rest.mm0`, states what remains
//! of Parts II and III of the spec as axioms over the model (`model.mm0`: the levels, the
//! denotation and the judgments), which is built over `lean-tg.mm0`, the encoding of the
//! spec's syntax with Part I's clauses proved in Tarski–Grothendieck set theory (`tg.mm0`),
//! `lean-tg2.mm0`, Part II's relations over level equivalence with their clauses proved, and
//! `lean-tg3.mm0`, the rest of Part II's relations over a judgment parameter, likewise.
//! The library's proofs are in the MMB file `abc` compiles, which a TG-mode certificate starts
//! with (`lean0 tg-link`).

/// The library's statement files, by name.
const FILES: &[(&str, &str)] = &[
    ("tg.mm0", include_str!("../../spec/tg/tg.mm0")),
    ("basic.mm0", include_str!("../../spec/tg/basic.mm0")),
    ("pairs.mm0", include_str!("../../spec/tg/pairs.mm0")),
    ("relations.mm0", include_str!("../../spec/tg/relations.mm0")),
    ("omega.mm0", include_str!("../../spec/tg/omega.mm0")),
    ("ordinals.mm0", include_str!("../../spec/tg/ordinals.mm0")),
    ("lfp.mm0", include_str!("../../spec/tg/lfp.mm0")),
    ("universe.mm0", include_str!("../../spec/tg/universe.mm0")),
    ("hartogs.mm0", include_str!("../../spec/tg/hartogs.mm0")),
    ("arith.mm0", include_str!("../../spec/tg/arith.mm0")),
    ("arith2.mm0", include_str!("../../spec/tg/arith2.mm0")),
    ("seq.mm0", include_str!("../../spec/tg/seq.mm0")),
    ("cont.mm0", include_str!("../../spec/tg/cont.mm0")),
    ("trees.mm0", include_str!("../../spec/tg/trees.mm0")),
    ("sorts.mm0", include_str!("../../spec/tg/sorts.mm0")),
    ("horn.mm0", include_str!("../../spec/tg/horn.mm0")),
    ("all.mm0", include_str!("../../spec/tg/all.mm0")),
    ("lean-tg.mm0", include_str!("../../spec/tg/lean-tg.mm0")),
    ("model-levels.mm0", include_str!("../../spec/tg/model-levels.mm0")),
    ("lean-tg2.mm0", include_str!("../../spec/tg/lean-tg2.mm0")),
    ("lean-tg3.mm0", include_str!("../../spec/tg/lean-tg3.mm0")),
    ("model-den.mm0", include_str!("../../spec/tg/model-den.mm0")),
    ("model-meta.mm0", include_str!("../../spec/tg/model-meta.mm0")),
    ("model-core.mm0", include_str!("../../spec/tg/model-core.mm0")),
    ("model-ind.mm0", include_str!("../../spec/tg/model-ind.mm0")),
    ("model-rec.mm0", include_str!("../../spec/tg/model-rec.mm0")),
    ("model-nat.mm0", include_str!("../../spec/tg/model-nat.mm0")),
    ("model-tel.mm0", include_str!("../../spec/tg/model-tel.mm0")),
    ("model-wf.mm0", include_str!("../../spec/tg/model-wf.mm0")),
    ("model-ctor.mm0", include_str!("../../spec/tg/model-ctor.mm0")),
    ("model-inv.mm0", include_str!("../../spec/tg/model-inv.mm0")),
    ("model-fold.mm0", include_str!("../../spec/tg/model-fold.mm0")),
    ("model-nst.mm0", include_str!("../../spec/tg/model-nst.mm0")),
    ("model-quot.mm0", include_str!("../../spec/tg/model-quot.mm0")),
    ("model-lit.mm0", include_str!("../../spec/tg/model-lit.mm0")),
    ("model-top.mm0", include_str!("../../spec/tg/model-top.mm0")),
    ("model-ci.mm0", include_str!("../../spec/tg/model-ci.mm0")),
    ("model.mm0", include_str!("../../spec/tg/model.mm0")),
    ("lean-tg-rest.mm0", include_str!("../../spec/tg/lean-tg-rest.mm0")),
];

/// The file certificates are verified against, with everything it imports.
pub const TOP: &str = "lean-tg-rest.mm0";

/// The text of `TOP` with everything it imports ([`crate::flatten`]).
pub fn text() -> Result<String, String> {
    crate::flatten(FILES, TOP)
}

/// The names the library declares, for the generator to leave alone so that a certificate's
/// statements read the same after the library as after the spec: its terms and definitions
/// with the notation tokens that look like identifiers, and its theorems and axioms (two
/// namespaces).
pub fn names() -> Result<(Vec<String>, Vec<String>), String> {
    let ident = |s: &str| s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    let (mut terms, mut thms) = (Vec::new(), Vec::new());
    for line in text()?.lines() {
        let mut words = line.split_whitespace().skip_while(|w| ["pure", "strict", "provable", "free", "local", "abstract", "pub"].contains(w));
        let (Some(kw), Some(rest)) = (words.next(), words.next()) else { continue };
        let name: String = rest.chars().take_while(|&c| c.is_ascii_alphanumeric() || c == '_').collect();
        match kw {
            "term" | "def" => terms.push(name),
            "axiom" | "theorem" => thms.push(name),
            "prefix" | "infixl" | "infixr" | "notation" => {
                terms.extend(line.split('$').skip(1).step_by(2).map(str::trim).filter(|t| ident(t)).map(String::from))
            }
            _ => {}
        }
    }
    Ok((terms, thms))
}
