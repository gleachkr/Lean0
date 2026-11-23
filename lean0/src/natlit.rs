//! Nat literals (audit §5): the theorems relating `lit n` to the environment's `Nat`, and
//! the theorems giving each operation the kernel computes on literals (nanoda's
//! `try_reduce_nat`) its value, guarded by the binary-arithmetic relations of `lean.mm0`.
//!
//! Stage B: for an operation with a schema in the spec (`EQS`: `Nat.add`, `Nat.pred`,
//! `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.shiftLeft`, `Nat.shiftRight`),
//! the defining equations Lean4Lean checks of the definition are derived over fresh
//! variables when it is declared (`eqs_theorem`: the theorem `Nat_add_eqs: add_eqs G Nat_add`),
//! and the operation's theorems on literals (`Nat_add_lit`, ...) follow from the spec's
//! rules. `natrec` does the same for the division-like operations (`Nat.div`, `Nat.mod`,
//! `Nat.gcd` and the bitwise operations), whose relations ask for proofs that lean0 carries
//! (`baked`). The equations of an operation that cannot be derived are an error: no axioms
//! are generated.
//!
//! One table (`OPS`) gives each operation's theorems. `op_axioms` states them, and the
//! elaborator instantiates them with `witness`.

use crate::elab::{mm, Elab, R};
use crate::gen::{add_thm, Vars};
use mm0kit::bin::Rel;
use mm0kit::env::{ThId, E, P};
use nanoda_lib::expr::BinderStyle;
use nanoda_lib::util::ExprPtr;
use num_bigint::{BigInt, BigUint, Sign};

/// An argument of a relation premise or of the operation: a variable of the theorem, or a
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
    /// The theorem is named `{op}_{suffix}`.
    pub suffix: &'static str,
    pub vars: &'static [&'static str],
    pub hyps: &'static [(Rel, &'static [A])],
    pub lhs: [A; 2],
    pub rhs: Rhs,
    /// The spec's rule it follows from, over the operation's `_eqs` theorem (`EQS`); its
    /// `bin` variables and premises are `vars` and `hyps` in this order.
    pub schema: Option<&'static str>,
}

pub struct Op {
    pub lean: &'static str,
    pub to_bool: bool,
    pub axs: &'static [OpAx],
}

use A::{N, V};

const ABC: &[&str] = &["a", "b", "c"];
const DIVMOD: &[&str] = &["a", "b", "q", "m", "r", "x"];
const DIVMOD_HYPS: &[(Rel, &[A])] = &[(Rel::Mul, &[V(1), V(2), V(3)]), (Rel::Add, &[V(3), V(4), V(0)]), (Rel::AddC, &[V(4), V(5), V(1)])];
const GCD: &[&str] = &["a", "b", "g", "p", "q", "x", "y", "m", "n"];
const GCD_DIV: [(Rel, &[A]); 4] =
    [(Rel::Mul, &[V(2), V(3), V(0)]), (Rel::Mul, &[V(2), V(4), V(1)]), (Rel::Mul, &[V(5), V(0), V(7)]), (Rel::Mul, &[V(6), V(1), V(8)])];
const SHR: &[&str] = &["a", "b", "p", "q", "m", "r", "x"];

const fn bin_op(suffix: &'static str, rel: Rel, schema: Option<&'static str>) -> OpAx {
    OpAx { suffix, vars: ABC, hyps: &[], lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)), schema }.with_hyp(rel)
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
    Op { lean: "Nat.add", to_bool: false, axs: &[bin_op("lit", Rel::Add, Some("nat_add_lit"))] },
    Op {
        lean: "Nat.sub",
        to_bool: false,
        axs: &[
            // c + b = a
            OpAx { suffix: "lit", vars: ABC, hyps: &[(Rel::Add, &[V(2), V(1), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)), schema: Some("nat_sub_lit") },
            // a + c = b, so a - b = 0
            OpAx { suffix: "lit0", vars: ABC, hyps: &[(Rel::Add, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::Lit(N(0)), schema: Some("nat_sub_lit0") },
        ],
    },
    Op { lean: "Nat.mul", to_bool: false, axs: &[bin_op("lit", Rel::Mul, Some("nat_mul_lit"))] },
    Op {
        lean: "Nat.div",
        to_bool: false,
        axs: &[
            // b q = m, m + r = a, r < b
            OpAx { suffix: "lit", vars: DIVMOD, hyps: DIVMOD_HYPS, lhs: [V(0), V(1)], rhs: Rhs::Lit(V(2)), schema: Some("nat_div_lit") },
            OpAx { suffix: "lit0", vars: &["a"], hyps: &[], lhs: [V(0), N(0)], rhs: Rhs::Lit(N(0)), schema: Some("nat_div_lit0") },
        ],
    },
    Op {
        lean: "Nat.mod",
        to_bool: false,
        axs: &[
            OpAx { suffix: "lit", vars: DIVMOD, hyps: DIVMOD_HYPS, lhs: [V(0), V(1)], rhs: Rhs::Lit(V(4)), schema: Some("nat_mod_lit") },
            OpAx { suffix: "lit0", vars: &["a"], hyps: &[], lhs: [V(0), N(0)], rhs: Rhs::Lit(V(0)), schema: Some("nat_mod_lit0") },
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
                schema: Some("nat_gcd_lit"),
            },
            OpAx {
                suffix: "lit2",
                vars: GCD,
                hyps: &[GCD_DIV[0], GCD_DIV[1], GCD_DIV[2], GCD_DIV[3], (Rel::Add, &[V(7), V(2), V(8)])],
                lhs: [V(0), V(1)],
                rhs: Rhs::Lit(V(2)),
                schema: Some("nat_gcd_lit2"),
            },
        ],
    },
    Op {
        lean: "Nat.beq",
        to_bool: true,
        axs: &[
            OpAx { suffix: "lit", vars: &["a"], hyps: &[], lhs: [V(0), V(0)], rhs: Rhs::True, schema: Some("nat_beq_lit") },
            // a + c + 1 = b
            OpAx { suffix: "lit_lt", vars: ABC, hyps: &[(Rel::AddC, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::False, schema: Some("nat_beq_lit_lt") },
            OpAx { suffix: "lit_gt", vars: ABC, hyps: &[(Rel::AddC, &[V(1), V(2), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::False, schema: Some("nat_beq_lit_gt") },
        ],
    },
    Op {
        lean: "Nat.ble",
        to_bool: true,
        axs: &[
            OpAx { suffix: "lit", vars: ABC, hyps: &[(Rel::Add, &[V(0), V(2), V(1)])], lhs: [V(0), V(1)], rhs: Rhs::True, schema: Some("nat_ble_lit") },
            OpAx { suffix: "lit_gt", vars: ABC, hyps: &[(Rel::AddC, &[V(1), V(2), V(0)])], lhs: [V(0), V(1)], rhs: Rhs::False, schema: Some("nat_ble_lit_gt") },
        ],
    },
    Op { lean: "Nat.land", to_bool: false, axs: &[bin_op("lit", Rel::And, Some("nat_land_lit"))] },
    Op { lean: "Nat.lor", to_bool: false, axs: &[bin_op("lit", Rel::Or, Some("nat_lor_lit"))] },
    Op { lean: "Nat.xor", to_bool: false, axs: &[bin_op("lit", Rel::Xor, Some("nat_xor_lit"))] },
    Op { lean: "Nat.pow", to_bool: false, axs: &[bin_op("lit", Rel::Pow, Some("nat_pow_lit"))] },
    Op {
        lean: "Nat.shiftLeft",
        to_bool: false,
        axs: &[OpAx {
            suffix: "lit",
            vars: &["a", "b", "p", "c"],
            hyps: &[(Rel::Pow, &[N(2), V(1), V(2)]), (Rel::Mul, &[V(0), V(2), V(3)])],
            lhs: [V(0), V(1)],
            rhs: Rhs::Lit(V(3)),
            schema: Some("nat_shl_lit"),
        }],
    },
    // With its equations (`shr_eqs`), the elaborator computes it a shift at a time instead
    // (`nat_shr_lit_z`/`nat_shr_lit_s`): no theorem is stated.
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
            schema: None,
        }],
    },
];

pub fn op(lean: &str) -> Option<&'static Op> { OPS.iter().find(|o| o.lean == lean) }

// ---------------------------------------------------------------- the defining equations

/// A term of a defining equation, over the fresh variables `x` (the outer one) and `y`, both
/// of type `Nat`.
#[derive(Clone, Copy)]
pub enum T {
    X,
    Y,
    Zero,
    Succ(&'static T),
    /// The definition, applied to two arguments (one for `Nat.pred`).
    F(&'static T, &'static T),
    F1(&'static T),
    /// The `i`th of `Eqs::fns`, applied.
    U(usize, &'static T, &'static T),
    U1(usize, &'static T),
    /// The literal `2`.
    Two,
    True,
    False,
}

/// `lhs ≡ rhs` over `vars` fresh variables (`x`, then `y`).
pub struct Eq {
    pub vars: u8,
    pub lhs: T,
    pub rhs: T,
}

/// The defining equations the spec's relation `rel` asks of a definition (`Primitive.lean`).
pub struct Eqs {
    pub lean: &'static str,
    /// `rel G f ...`, proved by `{rel}_i`.
    pub rel: &'static str,
    /// The definition's result type is `Bool` (its arguments `B t u` follow `f`).
    pub bool_result: bool,
    /// The other functions in the equations: those with equations of their own first
    /// (`deps`, whose relations' arguments follow in the spec: `mul_eqs G f fa` takes
    /// `add_eqs G fa`), then the rest (`shr_eqs G f fd` takes no equations of `Nat.div`).
    pub fns: &'static [&'static str],
    pub deps: usize,
    pub eqs: &'static [Eq],
}

use T::{Succ, Zero, F, F1, U, U1, X, Y};

const EQ_X0: Eq = Eq { vars: 1, lhs: F(&X, &Zero), rhs: X };

pub const EQS: &[Eqs] = &[
    Eqs {
        lean: "Nat.add",
        rel: "add_eqs",
        bool_result: false,
        fns: &[],
        deps: 0,
        eqs: &[EQ_X0, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: Succ(&F(&X, &Y)) }],
    },
    Eqs {
        lean: "Nat.pred",
        rel: "pred_eqs",
        bool_result: false,
        fns: &[],
        deps: 0,
        eqs: &[Eq { vars: 0, lhs: F1(&Zero), rhs: Zero }, Eq { vars: 1, lhs: F1(&Succ(&X)), rhs: X }],
    },
    Eqs {
        lean: "Nat.sub",
        rel: "sub_eqs",
        bool_result: false,
        fns: &["Nat.pred"],
        deps: 1,
        eqs: &[EQ_X0, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: U1(0, &F(&X, &Y)) }],
    },
    Eqs {
        lean: "Nat.mul",
        rel: "mul_eqs",
        bool_result: false,
        fns: &["Nat.add"],
        deps: 1,
        eqs: &[Eq { vars: 1, lhs: F(&X, &Zero), rhs: Zero }, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: U(0, &F(&X, &Y), &X) }],
    },
    Eqs {
        lean: "Nat.pow",
        rel: "pow_eqs",
        bool_result: false,
        fns: &["Nat.mul"],
        deps: 1,
        eqs: &[Eq { vars: 1, lhs: F(&X, &Zero), rhs: Succ(&Zero) }, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: U(0, &F(&X, &Y), &X) }],
    },
    Eqs {
        lean: "Nat.beq",
        rel: "beq_eqs",
        bool_result: true,
        fns: &[],
        deps: 0,
        eqs: &[
            Eq { vars: 0, lhs: F(&Zero, &Zero), rhs: T::True },
            Eq { vars: 1, lhs: F(&Zero, &Succ(&X)), rhs: T::False },
            Eq { vars: 1, lhs: F(&Succ(&X), &Zero), rhs: T::False },
            Eq { vars: 2, lhs: F(&Succ(&X), &Succ(&Y)), rhs: F(&X, &Y) },
        ],
    },
    Eqs {
        lean: "Nat.ble",
        rel: "ble_eqs",
        bool_result: true,
        fns: &[],
        deps: 0,
        eqs: &[
            Eq { vars: 1, lhs: F(&Zero, &X), rhs: T::True },
            Eq { vars: 1, lhs: F(&Succ(&X), &Zero), rhs: T::False },
            Eq { vars: 2, lhs: F(&Succ(&X), &Succ(&Y)), rhs: F(&X, &Y) },
        ],
    },
    Eqs {
        lean: "Nat.shiftLeft",
        rel: "shl_eqs",
        bool_result: false,
        fns: &["Nat.mul"],
        deps: 1,
        eqs: &[EQ_X0, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: F(&U(0, &T::Two, &X), &Y) }],
    },
    Eqs {
        lean: "Nat.shiftRight",
        rel: "shr_eqs",
        bool_result: false,
        fns: &["Nat.div"],
        deps: 0,
        eqs: &[EQ_X0, Eq { vars: 2, lhs: F(&X, &Succ(&Y)), rhs: U(0, &F(&X, &Y), &T::Two) }],
    },
];

pub fn eqs(lean: &str) -> Option<&'static Eqs> { EQS.iter().find(|e| e.lean == lean) }

/// Every operation with defining equations in the spec, here or in `natrec`.
pub fn eq_ops() -> impl Iterator<Item = &'static str> { EQS.iter().map(|e| e.lean).chain(crate::natrec::OPS.iter().map(|o| o.lean)) }

/// Exponents (of `Nat.pow`, and shift distances) beyond this are refused: the certificate
/// would be far too large anyway.
const MAX_EXPONENT: u64 = 1 << 20;

pub(crate) fn small(b: &BigUint) -> R<u32> {
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

/// The values of the variables of theorem `suffix` of `op` at `(a, b)`, or `None` if that
/// theorem does not apply.
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
        _ => return Err(format!("no literal theorem {op} {suffix}")),
    })
}

/// The theorems generated with `Nat.zero` and `Nat.succ`, and with each operation.
#[derive(Clone, Copy)]
pub struct NatLits {
    /// `deq G (lit b0) Nat.zero Nat`.
    pub zero: ThId,
    /// `bsucc a b > deq G (lit b) (Nat.succ (lit a)) Nat`.
    pub succ: ThId,
}

/// The translation of a constant without levels.
fn konst(el: &mut Elab<'_, '_, '_, '_>, lean: &str) -> Option<E> {
    el.g.const_term(lean, &[])
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
    // `Nat` is the spec's block `nat_D`: the spec's `lit_zero` and `lit_succ` tie the literals
    if el.g.env.has_term("nat_D") && el.g.env.has_thm("lit_zero") && el.g.env.has_thm("lit_succ")
        && el.g.consts["Nat"].term == el.g.env.term_id("nat_D") {
        let (zero, succ) = (el.g.env.thm_id("lit_zero"), el.g.env.thm_id("lit_succ"));
        el.g.nat = Some(NatLits { zero, succ });
        return Ok(())
    }
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

/// The spec has the literal operations' rules, and `Nat` is its block (so that the equations
/// can be stated over `nat_ty`).
fn spec_rules(el: &mut Elab<'_, '_, '_, '_>) -> bool {
    el.g.nat.is_some() && el.g.env.has_thm("add_eqs_i") && el.g.consts["Nat"].term == el.g.env.term_id("nat_D")
}

/// The arguments after `G` of `e.rel` (and of the rules over it): the definition, then for
/// a `Bool` result `Bool`, `true` and `false`, then the arguments of each dependency's
/// relation, then the other functions.
pub(crate) fn rel_args(el: &mut Elab<'_, '_, '_, '_>, e: &Eqs) -> Option<Vec<E>> {
    let mut v = vec![konst(el, e.lean)?];
    if e.bool_result {
        v.extend([konst(el, "Bool")?, konst(el, "Bool.true")?, konst(el, "Bool.false")?]);
    }
    for (i, &f) in e.fns.iter().enumerate() {
        if i < e.deps {
            v.extend(rel_args(el, eqs(f)?)?);
        } else {
            v.push(konst(el, f)?);
        }
    }
    Some(v)
}

/// Prove the definition's equations (`e`) over fresh variables and state `{cname}_eqs:
/// {rel} G f ...`, from `{rel}_i`. The definition is in the type checker's environment (the
/// driver extends it, `gen::run`).
fn eqs_theorem<'t>(el: &mut Elab<'_, '_, 't, '_>, e: &Eqs, cname: &str) -> R<ThId> {
    let Some(args) = rel_args(el, e) else { return Err("a function of the equations is not declared".into()) };
    let g = &mut *el.g;
    let gv = g.env.var(0);
    let mut targs = vec![gv];
    targs.extend(&args);
    let concl = g.env.app_n(e.rel, &targs);
    let name = g.thms.fresh(&format!("{cname}_eqs"));
    let doc = format!("`{}` has the defining equations of the spec's `{}` (Lean4Lean's `Primitive.lean`).", e.lean, e.rel);
    let args_g = g.g_args(&[]);
    if g.replay {
        return add_thm(&mut g.env, &name, args_g, vec![], concl, false, false, None, &doc)
    }
    if el.depth() != 0 {
        return Err("internal: the equations are derived at the top level".into())
    }
    // the premises, in the spec's order: the dependencies' relations, closedness, the type,
    // the equations
    let mut hyps: Vec<P> = Vec::new();
    for &f in &e.fns[..e.deps] {
        let Some(&th) = el.g.nat_eqs.get(f) else { return Err(format!("the equations of `{f}` were not derived")) };
        hyps.push(mm(el.g.env.thm(th, &[gv], &[]))?);
    }
    let g = &mut *el.g;
    // closed: the definition, `Bool`, `true` and `false`, and the functions without equations
    // (those with equations are closed by their relations)
    let zk = g.lean.nat(&mut g.env, 0);
    let nclosed = if e.bool_result { 4 } else { 1 };
    let uses = e.fns.len() - e.deps;
    for &c in args[..nclosed].iter().chain(&args[args.len() - uses..]) {
        hyps.push(mm(g.lean.closed(&mut g.env, zk, c))?);
    }
    let ty = g.consts[e.lean].ty_thm;
    hyps.push(mm(g.env.thm(ty, &[gv], &[]))?);
    let Some(nat_n) = el.tc.ctx.export_file.find_name("Nat") else { return Err("no `Nat`".into()) };
    let nat_e = {
        let ls = el.tc.ctx.alloc_levels_slice(&[]);
        el.tc.ctx.mk_const(nat_n, ls)
    };
    // the equations are about the definition, not the computation on literals that
    // short-circuits it (`Nat.beq 0 0`)
    el.tc.nat_ops_off = true;
    let r = eqs_derivations(el, e, nat_e, &mut hyps);
    el.tc.nat_ops_off = false;
    r?;
    let g = &mut *el.g;
    let p = mm(g.env.thm_n(&format!("{}_i", e.rel), &targs, &hyps))?;
    add_thm(&mut g.env, &name, args_g, vec![], concl, false, false, Some(p), &doc)
}

/// The derivations of the equations `e.eqs` over fresh variables, appended to `hyps`.
fn eqs_derivations<'t>(el: &mut Elab<'_, '_, 't, '_>, e: &Eqs, nat_e: ExprPtr<'t>, hyps: &mut Vec<P>) -> R<()> {
    for eq in e.eqs {
        let xs = ["x", "y"];
        for &x in &xs[..eq.vars as usize] {
            let n = el.tc.ctx.str1(x);
            el.open_pub(n, BinderStyle::Default, nat_e)?;
        }
        let r = (|| {
            let (lhs, rhs) = (term(el, e, &eq.lhs)?, term(el, e, &eq.rhs)?);
            el.defeq(lhs, rhs)
        })();
        for _ in 0..eq.vars {
            el.close_pub();
        }
        hyps.push(r?);
    }
    Ok(())
}

/// A term of an equation as a nanoda expression, over the open fvars.
fn term<'t>(el: &mut Elab<'_, '_, 't, '_>, e: &Eqs, t: &T) -> R<ExprPtr<'t>> {
    let cst = |el: &mut Elab<'_, '_, 't, '_>, name: &str| -> R<ExprPtr<'t>> {
        let Some(n) = el.tc.ctx.export_file.find_name(name) else { return Err(format!("no `{name}`")) };
        let ls = el.tc.ctx.alloc_levels_slice(&[]);
        Ok(el.tc.ctx.mk_const(n, ls))
    };
    let local = |el: &mut Elab<'_, '_, 't, '_>, i: usize| -> R<ExprPtr<'t>> {
        el.local(i).ok_or_else(|| "internal: an equation's variable is not open".to_string())
    };
    Ok(match *t {
        X => local(el, 0)?,
        Y => local(el, 1)?,
        Zero => cst(el, "Nat.zero")?,
        Succ(a) => {
            let (f, a) = (cst(el, "Nat.succ")?, term(el, e, a)?);
            el.tc.ctx.mk_app(f, a)
        }
        F(a, b) => {
            let (f, a, b) = (cst(el, e.lean)?, term(el, e, a)?, term(el, e, b)?);
            let fa = el.tc.ctx.mk_app(f, a);
            el.tc.ctx.mk_app(fa, b)
        }
        F1(a) => {
            let (f, a) = (cst(el, e.lean)?, term(el, e, a)?);
            el.tc.ctx.mk_app(f, a)
        }
        U(i, a, b) => {
            let (f, a, b) = (cst(el, e.fns[i])?, term(el, e, a)?, term(el, e, b)?);
            let fa = el.tc.ctx.mk_app(f, a);
            el.tc.ctx.mk_app(fa, b)
        }
        U1(i, a) => {
            let (f, a) = (cst(el, e.fns[i])?, term(el, e, a)?);
            el.tc.ctx.mk_app(f, a)
        }
        T::Two => el.tc.ctx.mk_nat_lit_quick(BigUint::from(2u32)).ok_or("internal: no literal 2")?,
        T::True => cst(el, "Bool.true")?,
        T::False => cst(el, "Bool.false")?,
    })
}

/// After the definition `lean` (MM0 constant `cname`, of type `ty`): if the spec has a
/// relation for it (`EQS`, `natrec::OPS`), prove it (`{cname}_eqs`); if it is one of the
/// operations the kernel computes on literals, with the expected type, state its theorems
/// on literals, proved from the spec's rules. A relation that is not proved is an error.
pub fn op_axioms<'t>(el: &mut Elab<'_, '_, 't, '_>, lean: &str, cname: &str, ty: ExprPtr<'t>) -> R<()> {
    if el.g.nat.is_none() {
        return Ok(())
    }
    let rec_op = crate::natrec::op(lean);
    if eqs(lean).is_some() || rec_op.is_some() {
        if spec_rules(el) {
            let (order0, pfs0) = (el.g.env.order.len(), el.g.env.num_pfs());
            let r = match (eqs(lean), rec_op) {
                (Some(e), _) => eqs_theorem(el, e, cname),
                (None, Some(o)) => crate::natrec::eqs_theorem(el, o, cname),
                _ => unreachable!(),
            };
            match r {
                Ok(th) => {
                    el.g.nat_eqs.insert(lean.to_string(), th);
                    el.g.lit_stage_b += 1;
                }
                Err(why) => {
                    el.g.rollback(order0, pfs0, &[]);
                    el.forget_proofs();
                    return Err(format!("the equations of `{lean}` are not derived ({why}): no axioms are generated for a literal operation"))
                }
            }
        } else {
            return Err(format!("`{lean}`: the spec's `Nat` is not the environment's, and no axioms are generated for a literal operation"))
        }
    }
    let Some(o) = op(lean) else { return Ok(()) };
    let nat = konst(el, "Nat").unwrap();
    let (res, tt, ff) = if o.to_bool {
        let (Some(b), Some(t), Some(f)) = (konst(el, "Bool"), konst(el, "Bool.true"), konst(el, "Bool.false")) else { return Ok(()) };
        (b, Some(t), Some(f))
    } else {
        (nat, None, None)
    };
    let Some(f) = konst(el, lean) else { return Ok(()) };
    let t = el.tr(ty)?;
    let eqs_th = el.g.nat_eqs.get(lean).copied();
    let rel_args = match (eqs(lean), rec_op) {
        (Some(e), _) => rel_args(el, e).unwrap_or_default(),
        (None, Some(o)) => crate::natrec::rel_args(el, o).unwrap_or_default(),
        _ => Vec::new(),
    };
    let g = &mut *el.g;
    let r1 = g.lean.pi(&mut g.env, nat, res);
    let want = g.lean.pi(&mut g.env, nat, r1);
    if t != want {
        return Ok(())
    }
    if lean == "Nat.shiftRight" && eqs_th.is_some() {
        // computed a shift at a time by the elaborator (`Elab::nat_shr`)
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
        let th = match (ax.schema, eqs_th) {
            (Some(rule), Some(eqs_th)) => {
                let doc = format!("`{lean}` on literals, from its defining equations (`{rule}`).");
                let p = if g.replay {
                    None
                } else {
                    let mut targs = vec![gv];
                    targs.extend(&rel_args);
                    targs.extend(&xs);
                    let mut ps = vec![mm(g.env.thm(eqs_th, &[gv], &[]))?];
                    ps.extend(hyps.iter().enumerate().map(|(i, &h)| g.env.hyp(i as u16, h)));
                    let p = mm(g.env.thm_n(rule, &targs, &ps))?;
                    Some(mm(g.env.convert(p, concl))?)
                };
                add_thm(&mut g.env, &name, v.args, hyps, concl, false, false, p, &doc)?
            }
            _ => return Err(format!("`{lean}` on literals: no rule in the spec, and no axioms are generated for a literal operation")),
        };
        ths.push(th);
    }
    g.nat_ops.insert(lean.to_string(), ths);
    Ok(())
}
