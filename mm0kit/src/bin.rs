//! Binary numerals of `lean.mm0` (`b0`, `bd0`, `bd1`) and proofs of the arithmetic relations
//! over them (`bsucc`, `bdbl`, `badd`, `baddc`, `bmul`, `bpow`, `band`, `bor`, `bxor`), by
//! recursion on the bits. Numerals are canonical (no leading zero), and so are the results.

use crate::bail;
use crate::env::*;
use num_bigint::BigUint;
use rustc_hash::FxHashMap as HashMap;

/// A relation proved by `Bins::rel`. Every relation's last argument is the result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Rel {
    Succ,
    Dbl,
    Add,
    AddC,
    Mul,
    Pow,
    And,
    Or,
    Xor,
}

impl Rel {
    pub fn name(self) -> &'static str {
        match self {
            Rel::Succ => "bsucc",
            Rel::Dbl => "bdbl",
            Rel::Add => "badd",
            Rel::AddC => "baddc",
            Rel::Mul => "bmul",
            Rel::Pow => "bpow",
            Rel::And => "band",
            Rel::Or => "bor",
            Rel::Xor => "bxor",
        }
    }

    pub fn arity(self) -> usize {
        match self {
            Rel::Succ | Rel::Dbl => 1,
            _ => 2,
        }
    }
}

pub struct Bins {
    b0: TId,
    bd0: TId,
    bd1: TId,
    pub lit: TId,
    nums: HashMap<BigUint, E>,
    /// Proofs contain no variables, so they are shared by every statement.
    memo: HashMap<(Rel, BigUint, BigUint), (BigUint, P)>,
}

/// `(n / 2, n % 2 == 1)`.
fn split(n: &BigUint) -> (BigUint, bool) { (n >> 1u32, n.bit(0)) }

impl Bins {
    pub fn new(env: &Env) -> Self {
        Bins {
            b0: env.term_id("b0"),
            bd0: env.term_id("bd0"),
            bd1: env.term_id("bd1"),
            lit: env.term_id("lit"),
            nums: HashMap::default(),
            memo: HashMap::default(),
        }
    }

    /// Forget memoized proofs from proof node `n` on (see `Env::truncate_pfs`).
    pub fn forget_pfs(&mut self, n: usize) { self.memo.retain(|_, (_, p)| (p.0 as usize) < n); }

    /// Forget numerals from expression node `n` on (after `Env::compact_nodes`).
    pub fn forget_nodes(&mut self, n: usize) { self.nums.retain(|_, e| (e.0 as usize) < n); }

    /// The canonical numeral of `n`.
    pub fn num(&mut self, env: &mut Env, n: &BigUint) -> E {
        if let Some(&e) = self.nums.get(n) {
            return e
        }
        let mut e = env.app(self.b0, &[]);
        let mut v = BigUint::default();
        for i in (0..n.bits()).rev() {
            let b = n.bit(i);
            e = env.app(if b { self.bd1 } else { self.bd0 }, &[e]);
            v = (v << 1u32) + u32::from(b);
            self.nums.entry(v.clone()).or_insert(e);
        }
        self.nums.insert(n.clone(), e);
        e
    }

    /// The value of a numeral (canonical or not).
    pub fn val(&self, env: &Env, e: E) -> Option<BigUint> {
        match env.head(e)? {
            (t, []) if t == self.b0 => Some(BigUint::default()),
            (t, [a]) if t == self.bd0 => Some(self.val(env, *a)? << 1u32),
            (t, [a]) if t == self.bd1 => Some((self.val(env, *a)? << 1u32) + 1u32),
            _ => None,
        }
    }

    /// `lit n`.
    pub fn lit(&mut self, env: &mut Env, n: &BigUint) -> E {
        let b = self.num(env, n);
        env.app(self.lit, &[b])
    }

    /// The result of `rel` on `ins`, and a proof of `rel ins.. result`.
    pub fn rel(&mut self, env: &mut Env, rel: Rel, ins: &[BigUint]) -> Result<(BigUint, P)> {
        if ins.len() != rel.arity() {
            bail!("{rel:?} takes {} arguments", rel.arity())
        }
        let zero = BigUint::default();
        let (a, b) = (&ins[0], ins.get(1).unwrap_or(&zero));
        let key = (rel, a.clone(), b.clone());
        if let Some(r) = self.memo.get(&key) {
            return Ok(r.clone())
        }
        let r = match rel {
            Rel::Succ => self.succ(env, a)?,
            Rel::Dbl => self.dbl(env, a)?,
            Rel::Add => self.add(env, a, b)?,
            Rel::AddC => self.addc(env, a, b)?,
            Rel::Mul => self.mul(env, a, b)?,
            Rel::Pow => self.pow(env, a, b)?,
            Rel::And | Rel::Or | Rel::Xor => self.bitwise(env, rel, a, b)?,
        };
        self.memo.insert(key, r.clone());
        Ok(r)
    }

    fn nums<const N: usize>(&mut self, env: &mut Env, ns: [&BigUint; N]) -> [E; N] { ns.map(|n| self.num(env, n)) }

    fn succ(&mut self, env: &mut Env, a: &BigUint) -> Result<(BigUint, P)> {
        let r = a + 1u32;
        if a.bits() == 0 {
            return Ok((r, env.thm_n("bsucc_0", &[], &[])?))
        }
        let (h, odd) = split(a);
        let p = if odd {
            let (h1, ph) = self.rel(env, Rel::Succ, std::slice::from_ref(&h))?;
            let args = self.nums(env, [&h, &h1]);
            env.thm_n("bsucc_d1", &args, &[ph])?
        } else {
            let args = self.nums(env, [&h]);
            env.thm_n("bsucc_d0", &args, &[])?
        };
        Ok((r, p))
    }

    fn dbl(&mut self, env: &mut Env, a: &BigUint) -> Result<(BigUint, P)> {
        let r = a << 1u32;
        if a.bits() == 0 {
            return Ok((r, env.thm_n("bdbl_0", &[], &[])?))
        }
        let (h, odd) = split(a);
        let args = self.nums(env, [&h]);
        Ok((r, env.thm_n(if odd { "bdbl_d1" } else { "bdbl_d0" }, &args, &[])?))
    }

    fn add(&mut self, env: &mut Env, a: &BigUint, b: &BigUint) -> Result<(BigUint, P)> {
        let r = a + b;
        if a.bits() == 0 {
            let args = self.nums(env, [b]);
            return Ok((r, env.thm_n("badd_0l", &args, &[])?))
        }
        if b.bits() == 0 {
            let args = self.nums(env, [a]);
            return Ok((r, env.thm_n("badd_0r", &args, &[])?))
        }
        let ((a2, i), (b2, j)) = (split(a), split(b));
        let (sub, name) = match (i, j) {
            (false, false) => (Rel::Add, "badd_00"),
            (false, true) => (Rel::Add, "badd_01"),
            (true, false) => (Rel::Add, "badd_10"),
            (true, true) => (Rel::AddC, "badd_11"),
        };
        let (c, pc) = self.rel(env, sub, &[a2.clone(), b2.clone()])?;
        let args = self.nums(env, [&a2, &b2, &c]);
        Ok((r, env.thm_n(name, &args, &[pc])?))
    }

    fn addc(&mut self, env: &mut Env, a: &BigUint, b: &BigUint) -> Result<(BigUint, P)> {
        let r = a + b + 1u32;
        if a.bits() == 0 || b.bits() == 0 {
            let (x, name) = if a.bits() == 0 { (b, "baddc_0l") } else { (a, "baddc_0r") };
            let (c, pc) = self.rel(env, Rel::Succ, std::slice::from_ref(x))?;
            let args = self.nums(env, [x, &c]);
            return Ok((r, env.thm_n(name, &args, &[pc])?))
        }
        let ((a2, i), (b2, j)) = (split(a), split(b));
        let (sub, name) = match (i, j) {
            (false, false) => (Rel::Add, "baddc_00"),
            (false, true) => (Rel::AddC, "baddc_01"),
            (true, false) => (Rel::AddC, "baddc_10"),
            (true, true) => (Rel::AddC, "baddc_11"),
        };
        let (c, pc) = self.rel(env, sub, &[a2.clone(), b2.clone()])?;
        let args = self.nums(env, [&a2, &b2, &c]);
        Ok((r, env.thm_n(name, &args, &[pc])?))
    }

    fn mul(&mut self, env: &mut Env, a: &BigUint, b: &BigUint) -> Result<(BigUint, P)> {
        if b.bits() == 0 {
            let args = self.nums(env, [a]);
            return Ok((BigUint::default(), env.thm_n("bmul_0", &args, &[])?))
        }
        let (b2, odd) = split(b);
        let (c, pc) = self.rel(env, Rel::Mul, &[a.clone(), b2.clone()])?;
        let (d, pd) = self.rel(env, Rel::Dbl, std::slice::from_ref(&c))?;
        if odd {
            let (e, pe) = self.rel(env, Rel::Add, &[d.clone(), a.clone()])?;
            let args = self.nums(env, [a, &b2, &c, &d, &e]);
            Ok((e, env.thm_n("bmul_d1", &args, &[pc, pd, pe])?))
        } else {
            let args = self.nums(env, [a, &b2, &c, &d]);
            Ok((d, env.thm_n("bmul_d0", &args, &[pc, pd])?))
        }
    }

    fn pow(&mut self, env: &mut Env, a: &BigUint, b: &BigUint) -> Result<(BigUint, P)> {
        if b.bits() == 0 {
            let args = self.nums(env, [a]);
            return Ok((BigUint::from(1u32), env.thm_n("bpow_0", &args, &[])?))
        }
        let (b2, odd) = split(b);
        let (c, pc) = self.rel(env, Rel::Pow, &[a.clone(), b2.clone()])?;
        let (d, pd) = self.rel(env, Rel::Mul, &[c.clone(), c.clone()])?;
        if odd {
            let (e, pe) = self.rel(env, Rel::Mul, &[d.clone(), a.clone()])?;
            let args = self.nums(env, [a, &b2, &c, &d, &e]);
            Ok((e, env.thm_n("bpow_d1", &args, &[pc, pd, pe])?))
        } else {
            let args = self.nums(env, [a, &b2, &c, &d]);
            Ok((d, env.thm_n("bpow_d0", &args, &[pc, pd])?))
        }
    }

    fn bitwise(&mut self, env: &mut Env, rel: Rel, a: &BigUint, b: &BigUint) -> Result<(BigUint, P)> {
        let pfx = match rel {
            Rel::And => "band",
            Rel::Or => "bor",
            _ => "bxor",
        };
        let r = match rel {
            Rel::And => a & b,
            Rel::Or => a | b,
            _ => a ^ b,
        };
        if a.bits() == 0 {
            let args = self.nums(env, [b]);
            return Ok((r, env.thm_n(&format!("{pfx}_0l"), &args, &[])?))
        }
        if b.bits() == 0 {
            let args = self.nums(env, [a]);
            return Ok((r, env.thm_n(&format!("{pfx}_0r"), &args, &[])?))
        }
        let ((a2, i), (b2, j)) = (split(a), split(b));
        let (c, pc) = self.rel(env, rel, &[a2.clone(), b2.clone()])?;
        let name = format!("{pfx}_{}{}", u8::from(i), u8::from(j));
        // the result bit is set: `bd1 c`; else `bd0 c` (or `b0`) by `bdbl`, except for `bor_00`,
        // where both inputs are nonzero and so is `c`
        let set = match rel {
            Rel::And => i && j,
            Rel::Or => i || j,
            _ => i != j,
        };
        if set || rel == Rel::Or {
            let args = self.nums(env, [&a2, &b2, &c]);
            Ok((r, env.thm_n(&name, &args, &[pc])?))
        } else {
            let (d, pd) = self.rel(env, Rel::Dbl, std::slice::from_ref(&c))?;
            let args = self.nums(env, [&a2, &b2, &c, &d]);
            Ok((r, env.thm_n(&name, &args, &[pc, pd])?))
        }
    }
}
