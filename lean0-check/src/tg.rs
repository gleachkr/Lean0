//! The TG library (`spec/tg`), embedded: in TG mode a certificate is verified against this
//! text instead of the spec (audit §11). Its top file, `lean-tg-rest.mm0`, states what remains
//! of Parts II and III of the spec as axioms over the model (`model/model.mm0`: the levels, the
//! denotation and the judgments), which is built over `lean-tg.mm0`, the encoding of the
//! spec's syntax with Part I's clauses proved in Tarski–Grothendieck set theory (`tg.mm0`),
//! `lean-tg2.mm0`, Part II's relations over level equivalence with their clauses proved, and
//! `lean-tg3.mm0`, the rest of Part II's relations over a judgment parameter, likewise.
//! The library's proofs are in the MMB file `abc` compiles, which a TG-mode certificate starts
//! with (`lean0 tg-link`).

/// The library's statement files, by path under `spec/tg`: `tg.mm0` (the axioms), `set/` (the
/// set-theory library), `encoding/` (the spec's syntax and relations), `model/`.
const FILES: &[(&str, &str)] = &[
    ("tg.mm0", include_str!("../../spec/tg/tg.mm0")),
    ("set/basic.mm0", include_str!("../../spec/tg/set/basic.mm0")),
    ("set/pairs.mm0", include_str!("../../spec/tg/set/pairs.mm0")),
    ("set/relations.mm0", include_str!("../../spec/tg/set/relations.mm0")),
    ("set/omega.mm0", include_str!("../../spec/tg/set/omega.mm0")),
    ("set/ordinals.mm0", include_str!("../../spec/tg/set/ordinals.mm0")),
    ("set/lfp.mm0", include_str!("../../spec/tg/set/lfp.mm0")),
    ("set/universe.mm0", include_str!("../../spec/tg/set/universe.mm0")),
    ("set/hartogs.mm0", include_str!("../../spec/tg/set/hartogs.mm0")),
    ("set/arith.mm0", include_str!("../../spec/tg/set/arith.mm0")),
    ("set/arith2.mm0", include_str!("../../spec/tg/set/arith2.mm0")),
    ("set/seq.mm0", include_str!("../../spec/tg/set/seq.mm0")),
    ("set/cont.mm0", include_str!("../../spec/tg/set/cont.mm0")),
    ("set/trees.mm0", include_str!("../../spec/tg/set/trees.mm0")),
    ("set/sorts.mm0", include_str!("../../spec/tg/set/sorts.mm0")),
    ("set/horn.mm0", include_str!("../../spec/tg/set/horn.mm0")),
    ("set/all.mm0", include_str!("../../spec/tg/set/all.mm0")),
    ("encoding/lean-tg.mm0", include_str!("../../spec/tg/encoding/lean-tg.mm0")),
    ("model/model-levels.mm0", include_str!("../../spec/tg/model/model-levels.mm0")),
    ("encoding/lean-tg2.mm0", include_str!("../../spec/tg/encoding/lean-tg2.mm0")),
    ("encoding/lean-tg3.mm0", include_str!("../../spec/tg/encoding/lean-tg3.mm0")),
    ("model/model-den.mm0", include_str!("../../spec/tg/model/model-den.mm0")),
    ("model/model-meta.mm0", include_str!("../../spec/tg/model/model-meta.mm0")),
    ("model/model-core.mm0", include_str!("../../spec/tg/model/model-core.mm0")),
    ("model/model-ind.mm0", include_str!("../../spec/tg/model/model-ind.mm0")),
    ("model/model-rec.mm0", include_str!("../../spec/tg/model/model-rec.mm0")),
    ("model/model-nat.mm0", include_str!("../../spec/tg/model/model-nat.mm0")),
    ("model/model-tel.mm0", include_str!("../../spec/tg/model/model-tel.mm0")),
    ("model/model-wf.mm0", include_str!("../../spec/tg/model/model-wf.mm0")),
    ("model/model-ctor.mm0", include_str!("../../spec/tg/model/model-ctor.mm0")),
    ("model/model-inv.mm0", include_str!("../../spec/tg/model/model-inv.mm0")),
    ("model/model-fold.mm0", include_str!("../../spec/tg/model/model-fold.mm0")),
    ("model/model-nst.mm0", include_str!("../../spec/tg/model/model-nst.mm0")),
    ("model/model-quot.mm0", include_str!("../../spec/tg/model/model-quot.mm0")),
    ("model/model-lit.mm0", include_str!("../../spec/tg/model/model-lit.mm0")),
    ("model/model-top.mm0", include_str!("../../spec/tg/model/model-top.mm0")),
    ("model/model-ci.mm0", include_str!("../../spec/tg/model/model-ci.mm0")),
    ("model/model.mm0", include_str!("../../spec/tg/model/model.mm0")),
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
