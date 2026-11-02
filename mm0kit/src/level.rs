//! Proofs of level equivalence (`leqv`) from the axioms of `lean.mm0`, by normalization.
//!
//! A normal form is a right-nested `lmax` chain of items `ls^k atom`, sorted by atom, where an
//! atom is `lz`, a level variable, or `limax A p` (`A` normal, `p` a variable). The zero atom
//! sorts first. No item dominates another (same atom with a smaller offset, or a zero item
//! with an offset at most another item's). Two levels are proved equivalent when their normal
//! forms are equal. This is complete for `imax`-free levels. Otherwise the goal's variables are
//! abstracted to `lparam`s and split by cases (`leqv_cases`) on a parameter under an `imax`
//! until no such parameter is left, which makes the procedure complete (audit §4).

use crate::bail;
use crate::env::*;
use crate::lean::Lean;
use rustc_hash::FxHashMap as HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum L {
    Zero,
    Succ(E),
    Max(E, E),
    IMax(E, E),
    Var,
}

pub struct Levels {
    memo: HashMap<E, (E, P)>,
}

impl Default for Levels {
    fn default() -> Self { Self::new() }
}

impl Levels {
    pub fn new() -> Self { Levels { memo: HashMap::default() } }

    pub fn reset(&mut self) { self.memo.clear(); }

    fn view(lean: &Lean, env: &Env, e: E) -> L {
        let i = &lean.ids;
        match env.head(e) {
            None => L::Var,
            Some((t, [_])) if Some(t) == env.term_names.get("lparam").copied() => L::Var,
            Some((t, [])) if t == i.lz => L::Zero,
            Some((t, [a])) if t == i.ls => L::Succ(*a),
            Some((t, [a, b])) if t == i.lmax => L::Max(*a, *b),
            Some((t, [a, b])) if t == i.limax => L::IMax(*a, *b),
            _ => panic!("not a level: {}", env.show(e, &[])),
        }
    }

    fn refl(env: &mut Env, a: E) -> P { env.thm_n("leqv_refl", &[a], &[]).unwrap() }

    fn parts(env: &Env, p: P) -> (E, E) {
        match env.head(env.concl(p)) {
            Some((_, &[a, b])) => (a, b),
            _ => unreachable!(),
        }
    }

    fn symm(env: &mut Env, p: P) -> P {
        let (a, b) = Self::parts(env, p);
        env.thm_n("leqv_symm", &[a, b], &[p]).unwrap()
    }

    fn trans(env: &mut Env, p: P, q: P) -> P {
        let (a, b) = Self::parts(env, p);
        let (b2, c) = Self::parts(env, q);
        assert_eq!(b, b2, "leqv trans mismatch");
        env.thm_n("leqv_trans", &[a, b, c], &[p, q]).unwrap()
    }

    fn cong_max(env: &mut Env, p: P, q: P) -> P {
        let (a, b) = Self::parts(env, p);
        let (c, d) = Self::parts(env, q);
        env.thm_n("leqv_max", &[a, b, c, d], &[p, q]).unwrap()
    }

    fn cong_imax(env: &mut Env, p: P, q: P) -> P {
        let (a, b) = Self::parts(env, p);
        let (c, d) = Self::parts(env, q);
        env.thm_n("leqv_imax", &[a, b, c, d], &[p, q]).unwrap()
    }

    fn cong_succ(env: &mut Env, p: P) -> P {
        let (a, b) = Self::parts(env, p);
        env.thm_n("leqv_succ", &[a, b], &[p]).unwrap()
    }

    fn ax(env: &mut Env, name: &str, args: &[E]) -> P { env.thm_n(name, args, &[]).unwrap() }

    /// Split an item `ls^k atom` into `(k, atom)`.
    fn item(lean: &Lean, env: &Env, mut e: E) -> (usize, E) {
        let mut k = 0;
        while let L::Succ(a) = Self::view(lean, env, e) {
            k += 1;
            e = a;
        }
        (k, e)
    }

    fn succs(lean: &Lean, env: &mut Env, mut e: E, k: usize) -> E {
        for _ in 0..k {
            e = env.app(lean.ids.ls, &[e]);
        }
        e
    }

    fn is_zero_atom(lean: &Lean, env: &Env, a: E) -> bool { Self::view(lean, env, a) == L::Zero }

    fn key(lean: &Lean, env: &Env, atom: E) -> u64 {
        if Self::is_zero_atom(lean, env, atom) { 0 } else { 1 + atom.0 as u64 }
    }

    /// `lmax (ls^j a) (ls^k a) ≈ ls^k a`, for `j <= k`.
    fn dominate(lean: &Lean, env: &mut Env, j: usize, k: usize, a: E) -> P {
        let sk = Self::succs(lean, env, a, k);
        if j == k {
            return Self::ax(env, "lmax_idem", &[sk])
        }
        if j > 0 {
            let (x, y) = (Self::succs(lean, env, a, j - 1), Self::succs(lean, env, a, k - 1));
            let p1 = Self::ax(env, "lmax_succ", &[x, y]);
            let p2 = Self::dominate(lean, env, j - 1, k - 1, a);
            let p2 = Self::cong_succ(env, p2);
            return Self::trans(env, p1, p2)
        }
        if k == 1 {
            return Self::ax(env, "lmax_succ_self", &[a])
        }
        // lmax a (s^k a) ≈ lmax a (lmax (s^{k-1} a) (s^k a)) ≈ lmax (lmax a (s^{k-1} a)) (s^k a)
        //                ≈ lmax (s^{k-1} a) (s^k a) ≈ s^k a
        let d1 = Self::dominate(lean, env, k - 1, k, a);
        let ra = Self::refl(env, a);
        let d1s = Self::symm(env, d1);
        let p1 = Self::cong_max(env, ra, d1s);
        let sk1 = Self::succs(lean, env, a, k - 1);
        let p2 = Self::ax(env, "lmax_assoc", &[a, sk1, sk]);
        let p2 = Self::symm(env, p2);
        let d0 = Self::dominate(lean, env, 0, k - 1, a);
        let rsk = Self::refl(env, sk);
        let p3 = Self::cong_max(env, d0, rsk);
        let p = Self::trans(env, p1, p2);
        let p = Self::trans(env, p, p3);
        Self::trans(env, p, d1)
    }

    /// `lmax (ls^j lz) (ls^k b) ≈ ls^k b`, for `j <= k`.
    fn zdom(lean: &Lean, env: &mut Env, j: usize, k: usize, b: E) -> P {
        if j == 0 {
            let sk = Self::succs(lean, env, b, k);
            return Self::ax(env, "lmax_zero", &[sk])
        }
        let z = env.app(lean.ids.lz, &[]);
        let (x, y) = (Self::succs(lean, env, z, j - 1), Self::succs(lean, env, b, k - 1));
        let p1 = Self::ax(env, "lmax_succ", &[x, y]);
        let p2 = Self::zdom(lean, env, j - 1, k - 1, b);
        let p2 = Self::cong_succ(env, p2);
        Self::trans(env, p1, p2)
    }

    /// `lmax x y ≈ y` if item `x` is dominated by item `y`.
    fn absorbed(lean: &Lean, env: &mut Env, x: E, y: E) -> Option<P> {
        let (jx, ax) = Self::item(lean, env, x);
        let (ky, ay) = Self::item(lean, env, y);
        if ax == ay && jx <= ky {
            Some(Self::dominate(lean, env, jx, ky, ax))
        } else if Self::is_zero_atom(lean, env, ax) && jx <= ky {
            Some(Self::zdom(lean, env, jx, ky, ay))
        } else {
            None
        }
    }

    /// `lmax x C ≈ C'` for an item `x` and a normal chain `C`.
    fn insert(lean: &Lean, env: &mut Env, x: E, c: E) -> (E, P) {
        let (head, rest) = match Self::view(lean, env, c) {
            L::Max(h, r) => (h, Some(r)),
            _ => (c, None),
        };
        let mx = env.app(lean.ids.lmax, &[x, c]);
        // x absorbed by the head
        if let Some(p) = Self::absorbed(lean, env, x, head) {
            let Some(r) = rest else { return (c, p) };
            // lmax x (lmax h r) ≈ lmax (lmax x h) r ≈ lmax h r
            let a = Self::ax(env, "lmax_assoc", &[x, head, r]);
            let a = Self::symm(env, a);
            let rr = Self::refl(env, r);
            let q = Self::cong_max(env, p, rr);
            return (c, Self::trans(env, a, q))
        }
        // head absorbed by x
        if let Some(p) = Self::absorbed(lean, env, head, x) {
            let p = {
                let cm = Self::ax(env, "lmax_comm", &[x, head]);
                Self::trans(env, cm, p)
            };
            let Some(r) = rest else { return (x, p) };
            let a = Self::ax(env, "lmax_assoc", &[x, head, r]);
            let a = Self::symm(env, a);
            let rr = Self::refl(env, r);
            let q = Self::cong_max(env, p, rr);
            let p1 = Self::trans(env, a, q);
            let (c2, p2) = Self::insert(lean, env, x, r);
            return (c2, Self::trans(env, p1, p2))
        }
        // A zero item can be absorbed by a later item: walk it right if some item dominates it.
        let (_, ax) = Self::item(lean, env, x);
        let x_first = Self::key(lean, env, ax) < Self::key(lean, env, Self::item(lean, env, head).1);
        let zero_walk = Self::is_zero_atom(lean, env, ax) && rest.is_some_and(|r| Self::dominated_in(lean, env, x, r));
        if x_first && !zero_walk {
            return (mx, Self::refl(env, mx))
        }
        match rest {
            None => {
                let p = Self::ax(env, "lmax_comm", &[x, head]);
                (env.app(lean.ids.lmax, &[head, x]), p)
            }
            Some(r) => {
                // lmax x (lmax h r) ≈ lmax h (lmax x r)
                let p1 = Self::left_comm(lean, env, x, head, r);
                let (r2, p2) = Self::insert(lean, env, x, r);
                let rh = Self::refl(env, head);
                let p2 = Self::cong_max(env, rh, p2);
                (env.app(lean.ids.lmax, &[head, r2]), Self::trans(env, p1, p2))
            }
        }
    }

    fn dominated_in(lean: &Lean, env: &Env, x: E, c: E) -> bool {
        let (jx, _) = Self::item(lean, env, x);
        let mut cur = c;
        loop {
            let (h, r) = match Self::view(lean, env, cur) {
                L::Max(h, r) => (h, Some(r)),
                _ => (cur, None),
            };
            if Self::item(lean, env, h).0 >= jx {
                return true
            }
            match r {
                Some(r) => cur = r,
                None => return false,
            }
        }
    }

    /// `lmax x (lmax y r) ≈ lmax y (lmax x r)`.
    fn left_comm(_lean: &Lean, env: &mut Env, x: E, y: E, r: E) -> P {
        let a1 = Self::ax(env, "lmax_assoc", &[x, y, r]);
        let a1 = Self::symm(env, a1);
        let cm = Self::ax(env, "lmax_comm", &[x, y]);
        let rr = Self::refl(env, r);
        let c = Self::cong_max(env, cm, rr);
        let a2 = Self::ax(env, "lmax_assoc", &[y, x, r]);
        let p = Self::trans(env, a1, c);
        Self::trans(env, p, a2)
    }

    /// `lmax A B ≈ C` for normal `A`, `B`.
    fn merge(lean: &Lean, env: &mut Env, a: E, b: E) -> (E, P) {
        match Self::view(lean, env, a) {
            L::Max(x, r) => {
                let p1 = Self::ax(env, "lmax_assoc", &[x, r, b]);
                let (m, p2) = Self::merge(lean, env, r, b);
                let rx = Self::refl(env, x);
                let p2 = Self::cong_max(env, rx, p2);
                let (c, p3) = Self::insert(lean, env, x, m);
                let p = Self::trans(env, p1, p2);
                (c, Self::trans(env, p, p3))
            }
            _ => Self::insert(lean, env, a, b),
        }
    }

    /// `ls A ≈ B` for normal `A`.
    fn succ_chain(lean: &Lean, env: &mut Env, a: E) -> (E, P) {
        match Self::view(lean, env, a) {
            L::Max(x, r) => {
                let sx = env.app(lean.ids.ls, &[x]);
                let sr = env.app(lean.ids.ls, &[r]);
                let p1 = Self::ax(env, "lmax_succ", &[x, r]);
                let p1 = Self::symm(env, p1);
                let (r2, p2) = Self::succ_chain(lean, env, r);
                debug_assert_eq!(Self::parts(env, p2).0, sr);
                let rsx = Self::refl(env, sx);
                let p2 = Self::cong_max(env, rsx, p2);
                (env.app(lean.ids.lmax, &[sx, r2]), Self::trans(env, p1, p2))
            }
            _ => {
                let s = env.app(lean.ids.ls, &[a]);
                (s, Self::refl(env, s))
            }
        }
    }

    /// `limax A B ≈ C` for normal `A`, `B`.
    fn imax_nf(&mut self, lean: &Lean, env: &mut Env, a: E, b: E) -> (E, P) {
        let z = env.app(lean.ids.lz, &[]);
        let ia = env.app(lean.ids.limax, &[a, b]);
        if a == b {
            return (b, Self::ax(env, "limax_self", &[b]))
        }
        match Self::view(lean, env, b) {
            L::Zero => (z, Self::ax(env, "limax_zero", &[a])),
            L::Max(x, r) => {
                let p1 = Self::ax(env, "limax_max", &[a, x, r]);
                let (c1, q1) = self.imax_nf(lean, env, a, x);
                let (c2, q2) = self.imax_nf(lean, env, a, r);
                let q = Self::cong_max(env, q1, q2);
                let (c, p3) = Self::merge(lean, env, c1, c2);
                let p = Self::trans(env, p1, q);
                (c, Self::trans(env, p, p3))
            }
            L::Succ(b1) => {
                let p1 = Self::ax(env, "limax_succ", &[a, b1]);
                let (c, p2) = Self::merge(lean, env, a, b);
                (c, Self::trans(env, p1, p2))
            }
            L::IMax(c, p) => {
                let p1 = Self::ax(env, "limax_imax", &[a, c, p]);
                let (c1, q1) = self.imax_nf(lean, env, a, p);
                let ic = env.app(lean.ids.limax, &[c, p]);
                let q2 = Self::refl(env, ic);
                let q = Self::cong_max(env, q1, q2);
                let (r, p3) = Self::merge(lean, env, c1, ic);
                let pp = Self::trans(env, p1, q);
                (r, Self::trans(env, pp, p3))
            }
            L::Var => {
                let one = env.app(lean.ids.ls, &[z]);
                if Self::view(lean, env, a) == L::Zero {
                    (b, Self::ax(env, "limax_zero_l", &[b]))
                } else if a == one {
                    (b, Self::ax(env, "limax_one", &[b]))
                } else {
                    (ia, Self::refl(env, ia))
                }
            }
        }
    }

    /// The normal form of `l` and a proof of `leqv l nf`.
    pub fn norm(&mut self, lean: &Lean, env: &mut Env, l: E) -> (E, P) {
        if let Some(&r) = self.memo.get(&l) {
            return r
        }
        let r = match Self::view(lean, env, l) {
            L::Zero | L::Var => (l, Self::refl(env, l)),
            L::Succ(a) => {
                let (na, p) = self.norm(lean, env, a);
                let p = Self::cong_succ(env, p);
                let (nb, q) = Self::succ_chain(lean, env, na);
                (nb, Self::trans(env, p, q))
            }
            L::Max(a, b) => {
                let (na, p) = self.norm(lean, env, a);
                let (nb, q) = self.norm(lean, env, b);
                let pq = Self::cong_max(env, p, q);
                let (c, r) = Self::merge(lean, env, na, nb);
                (c, Self::trans(env, pq, r))
            }
            L::IMax(a, b) => {
                let (na, p) = self.norm(lean, env, a);
                let (nb, q) = self.norm(lean, env, b);
                let pq = Self::cong_imax(env, p, q);
                let (c, r) = self.imax_nf(lean, env, na, nb);
                (c, Self::trans(env, pq, r))
            }
        };
        self.memo.insert(l, r);
        r
    }

    /// A proof of `leqv a b`, if `a` and `b` are equivalent.
    pub fn equiv(&mut self, lean: &Lean, env: &mut Env, a: E, b: E) -> Result<P> {
        if a == b {
            return Ok(Self::refl(env, a))
        }
        let (na, pa) = self.norm(lean, env, a);
        let (nb, pb) = self.norm(lean, env, b);
        if na == nb {
            let pb = Self::symm(env, pb);
            return Ok(Self::trans(env, pa, pb))
        }
        self.by_cases(lean, env, a, b).map_err(|e| {
            Mm0Error(format!("levels not equivalent: {} vs {} ({})", env.show(a, &[]), env.show(b, &[]), e.0))
        })
    }

    // ------------------------------------------------------------------ case splits

    fn nat(env: &mut Env, n: usize) -> E {
        let mut e = env.app_n("z", &[]);
        for _ in 0..n {
            e = env.app_n("s", &[e]);
        }
        e
    }

    /// `lt m n`, for literal naturals.
    fn lt(env: &mut Env, m: usize, n: usize) -> P {
        let mut p = {
            let k = Self::nat(env, n - m - 1);
            env.thm_n("le_z", &[k], &[]).unwrap()
        };
        for d in 1..=m + 1 {
            let (a, b) = (Self::nat(env, d - 1), Self::nat(env, n - m - 1 + d - 1));
            p = env.thm_n("le_s", &[a, b], &[p]).unwrap();
        }
        let (me, ne) = (Self::nat(env, m), Self::nat(env, n));
        let target = env.app_n("lt", &[me, ne]);
        env.convert(p, target).unwrap()
    }

    fn lparam_idx(lean: &Lean, env: &Env, e: E) -> Option<usize> {
        match env.head(e) {
            Some((t, [n])) if Some(t) == env.term_names.get("lparam").copied() => lean.nat_val(env, *n),
            _ => None,
        }
    }

    /// `l` with each variable `vs[i]` replaced by `lparam i`.
    fn abstract_vars(lean: &Lean, env: &mut Env, l: E, vs: &[E]) -> Result<E> {
        if let Some(i) = vs.iter().position(|&v| v == l) {
            let n = Self::nat(env, i);
            return Ok(env.app_n("lparam", &[n]))
        }
        Ok(match Self::view(lean, env, l) {
            L::Zero => l,
            L::Var if Self::lparam_idx(lean, env, l).is_some() => bail!("level already has object-level parameters"),
            L::Var => unreachable!("every variable is in vs"),
            L::Succ(a) => {
                let a = Self::abstract_vars(lean, env, a, vs)?;
                env.app(lean.ids.ls, &[a])
            }
            L::Max(a, b) | L::IMax(a, b) => {
                let (a2, b2) = (Self::abstract_vars(lean, env, a, vs)?, Self::abstract_vars(lean, env, b, vs)?);
                let t = env.head(l).unwrap().0;
                env.app(t, &[a2, b2])
            }
        })
    }

    fn vars(lean: &Lean, env: &Env, l: E, out: &mut Vec<E>) {
        match Self::view(lean, env, l) {
            L::Zero => {}
            L::Var => {
                if Self::lparam_idx(lean, env, l).is_none() && !out.contains(&l) {
                    out.push(l)
                }
            }
            L::Succ(a) => Self::vars(lean, env, a, out),
            L::Max(a, b) | L::IMax(a, b) => {
                Self::vars(lean, env, a, out);
                Self::vars(lean, env, b, out);
            }
        }
    }

    /// `lsubst k l a l2`: returns `l2` and the proof (`l` is built from `lparam`s only).
    fn lsubst(lean: &Lean, env: &mut Env, k: usize, l: E, a: E) -> (E, P) {
        let ke = Self::nat(env, k);
        match Self::view(lean, env, l) {
            L::Zero => (l, env.thm_n("lsubst_z", &[ke, a], &[]).unwrap()),
            L::Succ(b) => {
                let (b2, p) = Self::lsubst(lean, env, k, b, a);
                (env.app(lean.ids.ls, &[b2]), env.thm_n("lsubst_s", &[ke, b, a, b2], &[p]).unwrap())
            }
            L::Max(b, c) | L::IMax(b, c) => {
                let (b2, pb) = Self::lsubst(lean, env, k, b, a);
                let (c2, pc) = Self::lsubst(lean, env, k, c, a);
                let t = env.head(l).unwrap().0;
                let r = if t == lean.ids.lmax { "lsubst_max" } else { "lsubst_imax" };
                (env.app(t, &[b2, c2]), env.thm_n(r, &[ke, b, c, a, b2, c2], &[pb, pc]).unwrap())
            }
            L::Var => {
                let m = Self::lparam_idx(lean, env, l).expect("lsubst on a variable");
                let me = Self::nat(env, m);
                if m == k {
                    (a, env.thm_n("lsubst_eq", &[ke, a], &[]).unwrap())
                } else if m < k {
                    let h = Self::lt(env, m, k);
                    (l, env.thm_n("lsubst_lt", &[ke, me, a], &[h]).unwrap())
                } else {
                    let h = Self::lt(env, k, m);
                    (l, env.thm_n("lsubst_gt", &[ke, me, a], &[h]).unwrap())
                }
            }
        }
    }

    /// `linst S l l2` where `S` lists `vs`: returns `l2` and the proof.
    fn linst(lean: &Lean, env: &mut Env, s: E, vs: &[E], l: E) -> (E, P) {
        match Self::view(lean, env, l) {
            L::Zero => (l, env.thm_n("linst_z", &[s], &[]).unwrap()),
            L::Succ(a) => {
                let (a2, p) = Self::linst(lean, env, s, vs, a);
                (env.app(lean.ids.ls, &[a2]), env.thm_n("linst_s", &[s, a, a2], &[p]).unwrap())
            }
            L::Max(a, b) | L::IMax(a, b) => {
                let (a2, pa) = Self::linst(lean, env, s, vs, a);
                let (b2, pb) = Self::linst(lean, env, s, vs, b);
                let t = env.head(l).unwrap().0;
                let r = if t == lean.ids.lmax { "linst_max" } else { "linst_imax" };
                (env.app(t, &[a2, b2]), env.thm_n(r, &[s, a, b, a2, b2], &[pa, pb]).unwrap())
            }
            L::Var => {
                let i = Self::lparam_idx(lean, env, l).expect("linst on a variable");
                // lnth (lcons v0 (lcons v1 ...)) i vs[i]
                let mut tails = vec![s];
                for _ in 0..i {
                    let Some((_, &[_, t])) = env.head(*tails.last().unwrap()) else { unreachable!() };
                    tails.push(t);
                }
                let Some((_, &[_, rest])) = env.head(tails[i]) else { unreachable!() };
                let mut p = env.thm_n("lnth_z", &[vs[i], rest], &[]).unwrap();
                for d in (0..i).rev() {
                    let Some((_, &[a, t])) = env.head(tails[d]) else { unreachable!() };
                    let n = Self::nat(env, i - d - 1);
                    p = env.thm_n("lnth_s", &[a, vs[i], t, n], &[p]).unwrap();
                }
                let ie = Self::nat(env, i);
                (vs[i], env.thm_n("linst_param", &[s, ie, vs[i]], &[p]).unwrap())
            }
        }
    }

    /// A parameter under an `imax` in a normal form, to split on.
    fn split_param(lean: &Lean, env: &Env, nf: E) -> Option<usize> {
        match Self::view(lean, env, nf) {
            L::IMax(a, b) => Self::lparam_idx(lean, env, b).or_else(|| Self::split_param(lean, env, a)),
            L::Max(a, b) => Self::split_param(lean, env, a).or_else(|| Self::split_param(lean, env, b)),
            L::Succ(a) => Self::split_param(lean, env, a),
            _ => None,
        }
    }

    /// `leqv l r` for `l`, `r` built from `lparam`s, by normalization and case splits.
    fn prove_closed(&mut self, lean: &Lean, env: &mut Env, l: E, r: E) -> Result<P> {
        let (nl, pl) = self.norm(lean, env, l);
        let (nr, pr) = self.norm(lean, env, r);
        if nl == nr {
            let pr = Self::symm(env, pr);
            return Ok(Self::trans(env, pl, pr))
        }
        let Some(k) = Self::split_param(lean, env, nl).or_else(|| Self::split_param(lean, env, nr)) else {
            bail!("normal forms differ: {} vs {}", env.show(nl, &[]), env.show(nr, &[]))
        };
        let z = env.app(lean.ids.lz, &[]);
        let ke = Self::nat(env, k);
        let pk = env.app_n("lparam", &[ke]);
        let spk = env.app(lean.ids.ls, &[pk]);
        let (l0, hl0) = Self::lsubst(lean, env, k, l, z);
        let (r0, hr0) = Self::lsubst(lean, env, k, r, z);
        let (l1, hl1) = Self::lsubst(lean, env, k, l, spk);
        let (r1, hr1) = Self::lsubst(lean, env, k, r, spk);
        let p0 = self.prove_closed(lean, env, l0, r0)?;
        let p1 = self.prove_closed(lean, env, l1, r1)?;
        env.thm_n("leqv_cases", &[ke, l, r, l0, r0, l1, r1], &[hl0, hr0, p0, hl1, hr1, p1])
    }

    fn by_cases(&mut self, lean: &Lean, env: &mut Env, a: E, b: E) -> Result<P> {
        let mut vs = Vec::new();
        Self::vars(lean, env, a, &mut vs);
        Self::vars(lean, env, b, &mut vs);
        let a2 = Self::abstract_vars(lean, env, a, &vs)?;
        let b2 = Self::abstract_vars(lean, env, b, &vs)?;
        let p = self.prove_closed(lean, env, a2, b2)?;
        let mut s = env.app_n("lnil", &[]);
        for &v in vs.iter().rev() {
            s = env.app_n("lcons", &[v, s]);
        }
        let (a3, ha) = Self::linst(lean, env, s, &vs, a2);
        let (b3, hb) = Self::linst(lean, env, s, &vs, b2);
        debug_assert_eq!((a3, b3), (a, b));
        env.thm_n("leqv_inst", &[s, a2, b2, a, b], &[p, ha, hb])
    }
}
