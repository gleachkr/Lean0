//! `LEAN0_COSTS`: where proof nodes go, by elaborator rule, summed over a run.
//!
//! Each cost centre is a named span of elaboration. Its *self* cost is the proof nodes created
//! inside it and not inside a nested centre; its *total* cost includes the nested ones (counted
//! once when a centre recurses into itself).

use std::collections::HashMap;

#[derive(Default)]
pub struct Costs {
    /// Open centres: name, proof count at entry, nodes made by nested centres.
    stack: Vec<(&'static str, usize, usize)>,
    /// Per centre: calls, self nodes, total nodes.
    totals: HashMap<&'static str, [u64; 3]>,
    /// Centre names by tag (`Env::pf_tags`); tag 0 is outside every centre.
    names: Vec<&'static str>,
    tags: HashMap<&'static str, u16>,
    /// `LEAN0_COSTS=NAME`: nodes made while the centre `NAME` is open get `UNDER` in their tag,
    /// so the bytes beneath it can be totalled.
    under: Option<String>,
    under_depth: usize,
}

pub const UNDER: u16 = 0x8000;

impl Costs {
    pub fn from_env() -> Option<Costs> {
        let v = std::env::var("LEAN0_COSTS").ok()?;
        let under = (!v.is_empty() && v != "1").then_some(v);
        Some(Costs { names: vec!["(outside)"], under, ..Costs::default() })
    }

    /// Open the centre `name` at proof count `n`; returns its tag.
    pub fn enter(&mut self, name: &'static str, n: usize) -> u16 {
        self.stack.push((name, n, 0));
        if self.under.as_deref() == Some(name) {
            self.under_depth += 1;
        }
        self.tag(name) | self.under_bit()
    }

    fn under_bit(&self) -> u16 { if self.under_depth > 0 { UNDER } else { 0 } }

    fn tag(&mut self, name: &'static str) -> u16 {
        if let Some(&t) = self.tags.get(name) {
            return t
        }
        let t = u16::try_from(self.names.len()).unwrap();
        self.names.push(name);
        self.tags.insert(name, t);
        t
    }

    /// Close the innermost centre at proof count `n`; returns the tag now current.
    pub fn exit(&mut self, n: usize) -> u16 {
        let (name, n0, child) = self.stack.pop().expect("unbalanced cost centres");
        if self.under.as_deref() == Some(name) {
            self.under_depth -= 1;
        }
        let total = n - n0;
        let recursive = self.stack.iter().any(|&(m, ..)| m == name);
        let t = self.totals.entry(name).or_default();
        t[0] += 1;
        t[1] += (total - child) as u64;
        if !recursive {
            t[2] += total as u64;
        }
        match self.stack.last_mut() {
            Some(parent) => {
                parent.2 += total;
                let up = parent.0;
                self.tag(up) | self.under_bit()
            }
            None => 0,
        }
    }

    /// Proof bytes by centre, then by rule (spec rules by name, other buckets as one line each).
    pub fn byte_report(&self, env: &mm0kit::env::Env, bc: &mm0kit::mmb::ByteCosts) -> String {
        use mm0kit::mmb::ByteCosts as B;
        let all: u64 = bc.bytes.values().sum();
        let pct = |n: u64| 100.0 * n as f64 / all.max(1) as f64;
        let (mut by_tag, mut by_rule): (HashMap<u16, u64>, HashMap<u32, u64>) = Default::default();
        let under: u64 = bc.bytes.iter().filter(|((t, _), _)| t & UNDER != 0).map(|(_, &n)| n).sum();
        for (&(t, r), &n) in &bc.bytes {
            let t = t & !UNDER;
            *by_tag.entry(t).or_default() += n;
            *by_rule.entry(r).or_default() += n;
        }
        let mut s = format!("bytes: {all} proof bytes\n");
        if let Some(u) = &self.under {
            s += &format!("bytes: under {u}\t{under}\t{:.1}%\n", pct(under));
        }
        let mut pairs: Vec<_> = bc.bytes.iter().collect();
        pairs.sort_by_key(|r| std::cmp::Reverse(*r.1));
        for (&(t, r), &n) in pairs.into_iter().take(30) {
            let t = t & !UNDER;
            let name = if r < bc.spec_thms { env.thms[r as usize].name.to_string() } else { format!("bucket {}", u32::MAX - r) };
            s += &format!("bytes: pair {} / {name}\t{n}\t{:.1}%\n", self.names[t as usize], pct(n));
        }
        let mut rows: Vec<_> = by_tag.into_iter().collect();
        rows.sort_by_key(|r| std::cmp::Reverse(r.1));
        for (t, n) in rows {
            s += &format!("bytes: centre {}\t{n}\t{:.1}%\n", self.names[t as usize], pct(n));
        }
        let mut rows: Vec<_> = by_rule.into_iter().collect();
        rows.sort_by_key(|r| std::cmp::Reverse(r.1));
        for (r, n) in rows.into_iter().take(40) {
            let name = match r {
                B::LOCAL => "(local lemma uses)".to_string(),
                B::GENERATED => "(generated axioms and theorems)".to_string(),
                B::CONV => "(conversions)".to_string(),
                B::REF_BYTES => "(references to saved steps)".to_string(),
                r => env.thms[r as usize].name.to_string(),
            };
            s += &format!("bytes: rule {name}\t{n}\t{:.1}%\n", pct(n));
        }
        s
    }

    /// The table, by self cost: centre, calls, self nodes, share of all, total nodes.
    pub fn report(&self, all: u64) -> String {
        let mut rows: Vec<_> = self.totals.iter().collect();
        rows.sort_by_key(|(_, t)| std::cmp::Reverse(t[1]));
        let mut s = String::from("costs: centre\tcalls\tself\tshare\ttotal\n");
        let outside = all.saturating_sub(rows.iter().map(|(_, t)| t[1]).sum());
        s += &format!("costs: (outside)\t\t{outside}\t{:.1}%\t\n", 100.0 * outside as f64 / all.max(1) as f64);
        for (name, t) in rows {
            let share = 100.0 * t[1] as f64 / all.max(1) as f64;
            s += &format!("costs: {name}\t{}\t{}\t{share:.1}%\t{}\n", t[0], t[1], t[2]);
        }
        s
    }
}

/// The proof nodes made with each rule, most first: spec rules by name, generated axioms and
/// local lemmas each as one line.
pub fn rule_report(env: &mm0kit::env::Env, spec_thms: usize) -> String {
    let Some(c) = &env.rule_counts else { return String::new() };
    let (mut generated, mut lemmas) = (0, 0);
    let mut rows: Vec<(String, u64)> = Vec::new();
    for (i, &n) in c.iter().enumerate() {
        if i < spec_thms {
            rows.push((env.thms[i].name.to_string(), n));
        } else if env.thms[i].local {
            lemmas += n;
        } else {
            generated += n;
        }
    }
    rows.push(("(generated axioms and theorems)".into(), generated));
    rows.push(("(local lemmas)".into(), lemmas));
    rows.sort_by_key(|r| std::cmp::Reverse(r.1));
    let all: u64 = rows.iter().map(|r| r.1).sum();
    let mut s = String::from("rules: rule\tnodes\tshare\n");
    for (name, n) in rows.iter().take_while(|r| r.1 > 0) {
        s += &format!("rules: {name}\t{n}\t{:.1}%\n", 100.0 * *n as f64 / all.max(1) as f64);
    }
    s
}
