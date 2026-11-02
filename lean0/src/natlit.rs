//! Nat literals (audit §5): the generated axioms relating `lit n` to the environment's
//! `Nat`, and one or more axioms for each operation the kernel computes on literals (nanoda's
//! `try_reduce_nat`), guarded by the binary-arithmetic relations of `lean.mm0`.
//!
//! One table (`OPS`) gives each operation's axioms. `op_axioms` states them, and the
//! elaborator instantiates them with `witness`.

use crate::elab::{Elab, R};
use crate::gen::{add_thm, Vars};
use nanoda_lib::util::ExprPtr;
use mm0kit::bin::Rel;
use mm0kit::env::{ThId, E};
use num_bigint::{BigInt, BigUint, Sign};

/// An argument of a relation premise or of the operation: a variable of the axiom, or a
/// numeral.
#[derive(Clone, Copy, Debug)]
pub enum A {
    V(usize),
    N(u32),
}

#[derive(Clone, Copy, Debug)]
pub enum Rhs {
    Lit(A),
    True,
    False,
}

/// `hyps > deq G (op (lit lhs0) (lit lhs1)) rhs T`, over `(G: ctx)` and the `bin` variables.
pub struct OpAx {
    /// The axiom is named `{op}_{suffix}`.
    pub suffix: &'static str,
    pub vars: &'static [&'static str],
    pub hyps: &'static [(Rel, &'static [A])],
    pub lhs: [A; 2],
    pub rhs: Rhs,
}

pub struct Op {
    pub lean: &'static str,
    pub to_bool: bool,
    pub axs: &'static [OpAx],
}

use A::{N, V};

const ABC: &[&str] = &["a", "b", "c"];
const DIVMOD: &[&str] = &["a", "b", "q", "m", "r", "x"];
const DIVMOD_HYPS: &[(Rel, &[A])] = &[(Rel::Mul, &[V(2), V(1), V(3)]), (Rel::Add, &[V(3), V(4), V(0)]), (Rel::AddC, &[V(4), V(5), V(1)])];
const GCD: &[&str] = &["a", "b", "g", "p", "q", "x", "y", "m", "n"];
const GCD_DIV: [(Rel, &[A]); 4] =
    [(Rel::Mul, &[V(2), V(3), V(0)]), (Rel::Mul, &[V(2), V(4), V(1)]), (Rel::Mul, &[V(5), V(0), V(7)]), (Rel::Mul, &[V(6), V(1), V(8)])];
const SHR: &[&str] = &["a", "b", "p", "q", "m", "r", "x"];

const fn bin_op(suffix: &'static str, rel: Rel) -> OpAx {
    OpAx { suffix, vars: ABC, hyps: &[], lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)) }.with_hyp(rel)
}

impl OpAx {
    const fn with_hyp(self, rel: Rel) -> OpAx {
        let hyps: &'static [(Rel, &'static [A])] = match rel {
            Rel::Add => &[(Rel::Add, &[V(0), V(1), V(2)])],
            Rel::Mul => &[(Rel::Mul, &[V(0), V(1), V(2)])],
            Rel::Pow => &[(Rel::Pow, &[V(0), V(1), V(2)])],
            Rel::And => &[(Rel::And, &[V(0), V(1), V(2)])],
            Rel::Or => &[(Rel::Or, &[V(0), V(1), V(2)])],
            _ => &[(Rel::Xor, &[V(0), V(1), V(2)])],
        };
        OpAx { hyps, ..self }
    }
}

pub const OPS: &[Op] = &[
    Op { lean: "Nat.add", to_bool: false, axs: &[bin_op("lit", Rel::Add)] },
    Op {
        lean: "Nat.sub",
        to_bool: false,
        axs: &[
            // b + c = a
            OpAx { suffix: "lit", vars: ABC, hyps: &[(Rel::Add, &[V(2), V(1), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)) },
            // a + c = b, so a - b = 0
            OpAx { suffix: "lit0", vars: ABC, hyps: &[(Rel::Add, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::Lit(N(0)) },
        ],
    },
    Op { lean: "Nat.mul", to_bool: false, axs: &[bin_op("lit", Rel::Mul)] },
    Op {
        lean: "Nat.div",
        to_bool: false,
        axs: &[
            // q b = m, m + r = a, r < b
            OpAx { suffix: "lit", vars: DIVMOD, hyps: DIVMOD_HYPS, lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)) },
            OpAx { suffix: "lit0", vars: &["a"], hyps: &[], lhs: [V(0), N(0)], rhs: Rhs::Lit(N(0)) },
        ],
    },
    Op {
        lean: "Nat.mod",
        to_bool: false,
        axs: &[
            OpAx { suffix: "lit", vars: DIVMOD, hyps: DIVMOD_HYPS, lhs: [V(0), V(1)], rhs: Rhs::Lit(V(4)) },
            OpAx { suffix: "lit0", vars: &["a"], hyps: &[], lhs: [V(0), N(0)], rhs: Rhs::Lit(V(0)) },
        ],
    },
    Op {
        lean: "Nat.gcd",
        to_bool: false,
        axs: &[
            // g p = a, g q = b, and x a = y b + g (or y b = x a + g): every common divisor divides g
            OpAx {
                suffix: "lit",
                vars: GCD,
                hyps: &[GCD_DIV[0], GCD_DIV[1], GCD_DIV[2], GCD_DIV[3], (Rel::Add, &[V(8), V(2), V(7)])],
                lhs: [V(0), V(1)],
                rhs: Rhs::Lit(V(2)),
            },
            OpAx {
                suffix: "lit2",
                vars: GCD,
                hyps: &[GCD_DIV[0], GCD_DIV[1], GCD_DIV[2], GCD_DIV[3], (Rel::Add, &[V(7), V(2), V(8)])],
                lhs: [V(0), V(1)],
                rhs: Rhs::Lit(V(2)),
            },
        ],
    },
    Op {
        lean: "Nat.beq",
        to_bool: true,
        axs: &[
            OpAx { suffix: "lit", vars: &["a"], hyps: &[], lhs: [V(0), V(0)], rhs: Rhs::True },
            // a + c + 1 = b
            OpAx { suffix: "lit_lt", vars: ABC, hyps: &[(Rel::AddC, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::False },
            OpAx { suffix: "lit_gt", vars: ABC, hyps: &[(Rel::AddC, &[V(1), V(2), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::False },
        ],
    },
    Op {
        lean: "Nat.ble",
        to_bool: true,
        axs: &[
            OpAx { suffix: "lit", vars: ABC, hyps: &[(Rel::Add, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::True },
            OpAx { suffix: "lit_gt", vars: ABC, hyps: &[(Rel::AddC, &[V(1), V(2), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::False },
        ],
    },
    Op { lean: "Nat.land", to_bool: false, axs: &[bin_op("lit", Rel::And)] },
    Op { lean: "Nat.lor", to_bool: false, axs: &[bin_op("lit", Rel::Or)] },
    Op { lean: "Nat.xor", to_bool: false, axs: &[bin_op("lit", Rel::Xor)] },
    Op { lean: "Nat.pow", to_bool: false, axs: &[bin_op("lit", Rel::Pow)] },
    Op {
        lean: "Nat.shiftLeft",
        to_bool: false,
        axs: &[OpAx {
            suffix: "lit",
            vars: &["a", "b", "p", "c"],
            hyps: &[(Rel::Pow, &[N(2), V(1), V(2)]), (Rel::Mul, &[V(0), V(2), V(3)])],
            lhs: [V(0), V(1)],
            rhs: Rhs::Lit(V(3)),
        }],
    },
    Op {
        lean: "Nat.shiftRight",
        to_bool: false,
        axs: &[OpAx {
            suffix: "lit",
            vars: SHR,
            // 2^b = p, q p = m, m + r = a, r < p
            hyps: &[(Rel::Pow, &[N(2), V(1), V(2)]), (Rel::Mul, &[V(3), V(2), V(4)]), (Rel::Add, &[V(4), V(5), V(0)]), (Rel::AddC, &[V(5), V(6), V(2)])],
            lhs: [V(0), V(1)],
            rhs: Rhs::Lit(V(3)),
        }],
    },
];

pub fn op(lean: &str) -> Option<&'static Op> { OPS.iter().find(|o| o.lean == lean) }

/// Exponents (of `Nat.pow`, and shift distances) beyond this are refused: the certificate
/// would be far too large anyway.
const MAX_EXPONENT: u64 = 1 << 20;

fn small(b: &BigUint) -> R<u32> {
    match u32::try_from(b) {
        Ok(k) if u64::from(k) <= MAX_EXPONENT => Ok(k),
        _ => Err(format!("exponent {b} is too large to certify")),
    }
}

/// `(g, s, t)` with `s a + t b = g = gcd a b`.
fn ext_gcd(a: &BigUint, b: &BigUint) -> (BigUint, BigInt, BigInt) {
    let (mut r0, mut r1) = (BigInt::from(a.clone()), BigInt::from(b.clone()));
    let (mut s0, mut s1) = (BigInt::from(1), BigInt::from(0));
    let (mut t0, mut t1) = (BigInt::from(0), BigInt::from(1));
    while r1.sign() != Sign::NoSign {
        let q = &r0 / &r1;
        (r0, r1) = (r1.clone(), &r0 - &q * &r1);
        (s0, s1) = (s1.clone(), &s0 - &q * &s1);
        (t0, t1) = (t1.clone(), &t0 - &q * &t1);
    }
    (r0.magnitude().clone(), s0, t0)
}

/// The values of the variables of axiom `suffix` of `op` at `(a, b)`, or `None` if that axiom
/// does not apply.
pub fn witness(op: &str, suffix: &str, a: &BigUint, b: &BigUint) -> R<Option<Vec<BigUint>>> {
    let z = BigUint::default();
    let one = BigUint::from(1u32);
    let (a, b) = (a.clone(), b.clone());
    Ok(match (op, suffix) {
        ("Nat.add", _) => Some(vec![a.clone(), b.clone(), a + b]),
        ("Nat.sub", "lit") => (a >= b).then(|| vec![a.clone(), b.clone(), &a - &b]),
        ("Nat.sub", _) => (a < b).then(|| vec![a.clone(), b.clone(), &b - &a]),
        ("Nat.mul", _) => Some(vec![a.clone(), b.clone(), a * b]),
        ("Nat.div" | "Nat.mod", "lit") => (b != z).then(|| {
            let (q, r) = (&a / &b, &a % &b);
            vec![a.clone(), b.clone(), q.clone(), &q * &b, r.clone(), &b - &r - 1u32]
        }),
        ("Nat.div" | "Nat.mod", _) => (b == z).then(|| vec![a]),
        ("Nat.gcd", _) => {
            let (g, s, t) = ext_gcd(&a, &b);
            let (p, q) = if g == z { (z.clone(), z.clone()) } else { (&a / &g, &b / &g) };
            // s ≥ 0 ≥ t gives x a = y b + g ("lit"); s ≤ 0 ≤ t gives y b = x a + g ("lit2")
            let first = s.sign() != Sign::Minus && t.sign() != Sign::Plus;
            if first != (suffix == "lit") {
                return Ok(None)
            }
            let (x, y) = (s.magnitude().clone(), t.magnitude().clone());
            let (m, n) = (&x * &a, &y * &b);
            Some(vec![a, b, g, p, q, x, y, m, n])
        }
        ("Nat.beq", "lit") => (a == b).then(|| vec![a]),
        ("Nat.beq", "lit_lt") => (a < b).then(|| vec![a.clone(), b.clone(), &b - &a - 1u32]),
        ("Nat.beq", _) => (a > b).then(|| vec![a.clone(), b.clone(), &a - &b - 1u32]),
        ("Nat.ble", "lit") => (a <= b).then(|| vec![a.clone(), b.clone(), &b - &a]),
        ("Nat.ble", _) => (a > b).then(|| vec![a.clone(), b.clone(), &a - &b - 1u32]),
        ("Nat.land", _) => Some(vec![a.clone(), b.clone(), &a & &b]),
        ("Nat.lor", _) => Some(vec![a.clone(), b.clone(), &a | &b]),
        ("Nat.xor", _) => Some(vec![a.clone(), b.clone(), &a ^ &b]),
        ("Nat.pow", _) => {
            let k = small(&b)?;
            Some(vec![a.clone(), b, a.pow(k)])
        }
        ("Nat.shiftLeft", _) => {
            let p = one << small(&b)?;
            Some(vec![a.clone(), b, p.clone(), a * p])
        }
        ("Nat.shiftRight", _) => {
            let p = one << small(&b)?;
            let (q, r) = (&a / &p, &a % &p);
            Some(vec![a.clone(), b, p.clone(), q.clone(), &q * &p, r.clone(), &p - &r - 1u32])
        }
        _ => return Err(format!("no literal axiom {op} {suffix}")),
    })
}

/// The axioms generated with `Nat.zero` and `Nat.succ`, and with each operation.
#[derive(Clone, Copy)]
pub struct NatLits {
    /// `deq G (lit b0) Nat.zero Nat`.
    pub zero: ThId,
    /// `bsucc a b > deq G (lit b) (Nat.succ (lit a)) Nat`.
    pub succ: ThId,
}

/// The translation of a constant without levels.
fn konst(el: &mut Elab<'_, '_, '_, '_>, lean: &str) -> Option<E> {
    let t = el.g.consts.get(lean)?.term;
    (el.g.consts[lean].nlevels == 0).then(|| el.g.env.app(t, &[]))
}

/// Once `Nat`, `Nat.zero` and `Nat.succ` are declared with the expected types
/// (`Nat.zero : Nat`, `Nat.succ : Nat → Nat`), state `Nat_lit_zero` and `Nat_lit_succ`.
/// These make `lit n` mean `Nat.succ^n Nat.zero`. Otherwise there are no literal axioms, and
/// a literal cannot be certified.
///
/// Called with the constructor `cur` being declared, of type `cur_ty` (it is not yet in the
/// type checker's environment).
pub fn lit_axioms<'t>(el: &mut Elab<'_, '_, 't, '_>, cur: &str, cur_ty: ExprPtr<'t>) -> R<()> {
    if el.g.nat.is_some() {
        return Ok(())
    }
    let (Some(nat), Some(zero), Some(succ)) = (konst(el, "Nat"), konst(el, "Nat.zero"), konst(el, "Nat.succ")) else { return Ok(()) };
    let nc = el.tc.ctx.export_file.name_cache;
    let ty_of = |lean: &str, n: Option<nanoda_lib::util::NamePtr<'t>>| -> Option<ExprPtr<'t>> {
        if lean == cur { Some(cur_ty) } else { el.tc.env.get_declar(&n?).map(|d| d.info().ty) }
    };
    let (Some(tz), Some(ts)) = (ty_of("Nat.zero", nc.nat_zero), ty_of("Nat.succ", nc.nat_succ)) else { return Ok(()) };
    let (tz, ts) = (el.tr(tz)?, el.tr(ts)?);
    let g = &mut *el.g;
    let nn = g.lean.pi(&mut g.env, nat, nat);
    if tz != nat || ts != nn {
        return Ok(())
    }
    let zero_b = g.bins.num(&mut g.env, &BigUint::default());
    let lit0 = g.env.app(g.bins.lit, &[zero_b]);
    let mut v = Vars::new();
    let gv = v.add(&mut g.env, "G", "ctx");
    let concl = g.lean.deq(&mut g.env, gv, lit0, zero, nat);
    let name = g.thms.fresh("Nat_lit_zero");
    let th0 = add_thm(&mut g.env, &name, v.args, vec![], concl, true, false, None, "The literal `0` is `Nat.zero`.")?;
    let mut v = Vars::new();
    let gv = v.add(&mut g.env, "G", "ctx");
    let (a, b) = (v.add(&mut g.env, "a", "bin"), v.add(&mut g.env, "b", "bin"));
    let (la, lb) = (g.env.app(g.bins.lit, &[a]), g.env.app(g.bins.lit, &[b]));
    let sa = g.lean.app(&mut g.env, succ, la);
    let hyp = g.env.app_n("bsucc", &[a, b]);
    let concl = g.lean.deq(&mut g.env, gv, lb, sa, nat);
    let name = g.thms.fresh("Nat_lit_succ");
    let th1 = add_thm(&mut g.env, &name, v.args, vec![hyp], concl, true, false, None, "The literal `n+1` is `Nat.succ n`.")?;
    g.nat = Some(NatLits { zero: th0, succ: th1 });
    Ok(())
}

/// After the definition `lean` (MM0 constant `cname`, of type `ty`): if it is one of the
/// operations the kernel computes on literals, with the expected type, state its axioms.
/// An operation without axioms cannot be certified on literals.
pub fn op_axioms<'t>(el: &mut Elab<'_, '_, 't, '_>, lean: &str, cname: &str, ty: ExprPtr<'t>) -> R<()> {
    let Some(o) = op(lean) else { return Ok(()) };
    if el.g.nat.is_none() {
        return Ok(())
    }
    let nat = konst(el, "Nat").unwrap();
    let (res, tt, ff) = if o.to_bool {
        let (Some(b), Some(t), Some(f)) = (konst(el, "Bool"), konst(el, "Bool.true"), konst(el, "Bool.false")) else { return Ok(()) };
        (b, Some(t), Some(f))
    } else {
        (nat, None, None)
    };
    let Some(f) = konst(el, lean) else { return Ok(()) };
    let t = el.tr(ty)?;
    let g = &mut *el.g;
    let r1 = g.lean.pi(&mut g.env, nat, res);
    let want = g.lean.pi(&mut g.env, nat, r1);
    if t != want {
        return Ok(())
    }
    let mut ths = Vec::new();
    for ax in o.axs {
        let mut v = Vars::new();
        let gv = v.add(&mut g.env, "G", "ctx");
        let xs: Vec<E> = ax.vars.iter().map(|s| v.add(&mut g.env, s, "bin")).collect();
        let arg = |g: &mut crate::gen::Gen, a: A| match a {
            A::V(i) => xs[i],
            A::N(k) => g.bins.num(&mut g.env, &BigUint::from(k)),
        };
        let hyps: Vec<E> = ax
            .hyps
            .iter()
            .map(|(rel, args)| {
                let es: Vec<E> = args.iter().map(|&a| arg(g, a)).collect();
                g.env.app_n(rel.name(), &es)
            })
            .collect();
        let (x, y) = (arg(g, ax.lhs[0]), arg(g, ax.lhs[1]));
        let (lx, ly) = (g.env.app(g.bins.lit, &[x]), g.env.app(g.bins.lit, &[y]));
        let fx = g.lean.app(&mut g.env, f, lx);
        let lhs = g.lean.app(&mut g.env, fx, ly);
        let rhs = match ax.rhs {
            Rhs::Lit(a) => {
                let n = arg(g, a);
                g.env.app(g.bins.lit, &[n])
            }
            Rhs::True => tt.unwrap(),
            Rhs::False => ff.unwrap(),
        };
        let concl = g.lean.deq(&mut g.env, gv, lhs, rhs, res);
        let name = g.thms.fresh(&format!("{cname}_{}", ax.suffix));
        let doc = format!("`{lean}` on literals (the kernel computes it with GMP).");
        ths.push(add_thm(&mut g.env, &name, v.args, hyps, concl, true, false, None, &doc)?);
    }
    g.nat_ops.insert(lean.to_string(), ths);
    Ok(())
}
