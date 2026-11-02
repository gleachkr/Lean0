//! Lean names to MM0 identifiers.

use std::collections::HashSet;

/// MM0 identifiers are `[a-zA-Z_][a-zA-Z0-9_]*` (and not `_`). Lean name separators become
/// `_`, a prime becomes `_p`, and any other character becomes `_u<hex>_`.
pub fn mangle(lean: &str) -> String {
    let mut out = String::new();
    for c in lean.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
            '.' => out.push('_'),
            '\'' => out.push_str("_p"),
            c => out.push_str(&format!("_u{:x}_", c as u32)),
        }
    }
    if out.is_empty() || out == "_" || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, 'x');
    }
    out
}

/// A namespace of MM0 identifiers that hands out fresh names.
#[derive(Default)]
/// Names in use, kept as hashes: there are millions (one per lemma), and a false match only
/// makes `fresh` skip a free name.
pub struct Names {
    used: HashSet<u64>,
}

/// SipHash: FxHash collides on similar names (`x_l94`), which would rename them.
fn hash(s: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::hash::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

impl Names {
    pub fn reserve(&mut self, s: &str) { self.used.insert(hash(s)); }

    pub fn contains(&self, s: &str) -> bool { self.used.contains(&hash(s)) }

    pub fn approx_bytes(&self) -> usize { self.used.capacity() * 9 }

    /// `base` if it is free, else `base_1`, `base_2`, ... Names starting with
    /// `mm0kit::lean::FACT_PREFIX` are left to mm0kit's shared lemmas: such a base gets an `x`
    /// in front.
    pub fn fresh(&mut self, base: &str) -> String {
        let base = &if base.starts_with(mm0kit::lean::FACT_PREFIX) { format!("x{base}") } else { base.to_string() };
        let mut s = base.to_string();
        let mut i = 1;
        while self.contains(&s) {
            s = format!("{base}_{i}");
            i += 1;
        }
        self.reserve(&s);
        s
    }
}
