# Audit: `spec/lean.mm0` against Lean4Lean (@ 67f63b0)

Scope: every axiom in `spec/lean.mm0`. §1–3 audit the core rules (the spec's first 204 lines
at the time); §4–8 argue the additions since, §9 the notations, and §10 describes how the
encoding departs from Lean4Lean's presentation. Lean4Lean paths are relative to
`refs/lean4lean/Lean4Lean/` (`scripts/fetch-refs.sh`). The model-search scripts mentioned
below (`build/audit/`) are not part of the repository.

**Bottom line: no soundness problem found.** Every axiom holds in the intended model, and
every `deq` axiom is a verbatim instance of an `IsDefEq` constructor. The real gaps are about
**completeness**: the `leqv` axioms cannot derive some valid level equivalences that nanoda
accepts (§3, issue 1), and `constDF` for `def`-encoded constants is not directly available
(issue 2).

## 1. Soundness argument (why a per-axiom check is enough)

Every axiom in the file is a Horn clause over closed first-order terms. `wff` has no
connectives, there is no negation, and no sort admits bound or dummy variables (`strict`,
`mm0.md:82`). So an MM0 derivation is a finite tree of schematic axiom instances, and the
system is sound for the intended reading if every axiom is valid in this **standard model**:

| MM0 | interpreted as |
|---|---|
| `nat` terms `z`, `s` | `Nat` |
| `le`, `add`, `lt` | `≤`, graph of `+`, `<` |
| `lvl` terms | `VLevel` (`lz/ls/lmax/limax` ↦ `zero/succ/max/imax`) |
| `leqv a b` | `a ≈ b`, i.e. `a.eval = b.eval` (VLevel.lean:58) |
| `expr` terms | `VExpr` (`pi` ↦ `forallE`); later generated `term` constants ↦ `.const c ls` |
| `closed k e` | `ClosedN e k` (VExpr.lean:99) |
| `lift n k e e2` | `e2 = liftN n e k` (VExpr.lean:38) |
| `inst k e a e2` | `e2 = inst e a k` (VExpr.lean:240) |
| `lookup G n A` | `Lookup G n A` (Typing/Basic.lean:6) |
| `deq G e e2 A` | `env.IsDefEq U G e e2 A` (Typing/Basic.lean:18) |
| `inh G A` | `∃ e, env.HasType U G e A` |

Consequences:

* **Functionality.** `lift`, `inst` and `lookup` are interpreted as graphs of functions, and
  every axiom about them (including the `*_closed` shortcuts) holds in the model. So every
  derivable `lift n k e e2` has `e2 = liftN n e k`, and the same goes for `inst` and `lookup`.
  Overlapping rules always agree: `lift_closed` and the structural rules, for example, give the
  same answer. There is no way to get two different results.
* **WF conditions.** Lean4Lean needs `l.WF U` only in `sortDF`, `constDF` and `extra`. Because
  `lvl` is `strict` (no dummies), every level term in a proof of a theorem with level variables
  `u₀ … uₙ₋₁` is built from those variables and `lz/ls/lmax/limax`. Map `uᵢ ↦ .param i` and take
  `U = n`. Then every level in the derivation satisfies `WF n`, and the dropped premises hold.
  Using a lemma at an instance (MM0 substitution of `lvl` variables) is justified by
  `IsDefEq.instL` (Typing/Lemmas.lean:595). If the proof uses a level variable that the
  statement does not need, instantiate it with `lz`. All the `leqv` laws are identities of
  `eval`, so they survive substitution of arbitrary `VLevel`s for their metavariables.
* **Variables that occur only in hypotheses** (`u` in `lamDF`/`defeqDF`, `A B` in `appDF`, `e2`
  in `trans`, `j` in `*_closed`, `B` in `lookup_s`, `B` in `beta`). In MM0 the proof supplies
  every axiom argument explicitly, and every sort is inhabited (`z`, `lz`, `srt lz`, `nil`). So
  this is just ordinary Horn-clause instantiation: no pitfall.
* `bvar` is both a `term` and an `axiom` name. Terms and theorems live in separate namespaces,
  and both mm0-zig and mm0-c accept the file (checked with `spec/examples/*`).

## 2. Per-axiom table

Verdicts: **T** means a faithful transcription of a constructor or defining equation. **A**
means a sound admissible fact (lemma cited, hypotheses checked). **L** means a valid level law
(checked by cases on `eval` with `imax a b = if b = 0 then 0 else max a b`; Lean core
`Nat.imax`, used at VLevel.lean:38). **D** means a conservative `def`.

### Naturals

| axiom (spec line) | verdict | justification |
|---|---|---|
| `le_z` (34) | T | `0 ≤ n` |
| `le_s` (35) | T | `i ≤ n → i+1 ≤ n+1`. With `le_z` this is the least relation, i.e. exactly `≤` |
| `lt` (38, def) | D | `i < n :≡ i+1 ≤ n` (Nat.lt is defined this way) |
| `add_z` (42) | T | `i + 0 = i` |
| `add_s` (43) | T | `i + n = j → i + (n+1) = j+1`. The relation is exactly the graph of `+` |

### Levels (`leqv` = `≈`, VLevel.lean:58)

| axiom | verdict | justification |
|---|---|---|
| `leqv_refl/symm/trans` (62-64) | L | equality of `eval` functions is an equivalence |
| `leqv_succ` (65) | L | `succ_congr` VLevel.lean:74 |
| `leqv_max` (66) | L | `max_congr` VLevel.lean:80 |
| `leqv_imax` (68) | L | `imax_congr` VLevel.lean:83 |
| `lmax_comm` (70) | L | `max_comm` VLevel.lean:86 |
| `lmax_assoc` (71) | L | `Nat.max_assoc` pointwise |
| `lmax_idem` (72) | L | `max_self` VLevel.lean:94 |
| `lmax_zero` (73) | L | `max 0 a = a` (right variant via `lmax_comm`) |
| `lmax_succ` (74) | L | `max (a+1) (b+1) = max a b + 1` |
| `lmax_succ_self` (75) | L | `max a (a+1) = a+1` |
| `limax_zero` (76) | L | `imax_zero` VLevel.lean:99 |
| `limax_zero_l` (77) | L | `zero_imax` VLevel.lean:96 (`b=0`: 0; else `max 0 b = b`) |
| `limax_one` (added later) | L | not in the audited file; checked by hand: `a=0` gives `imax 1 0 = 0`; otherwise `max 1 a = a` since `a ≥ 1`. nanoda's `simplify` applies this rule (`imax 1 a ↦ a`). I found no derivation from the other axioms (it seems to need a case split on `a`), but did not prove it underivable |
| `limax_succ` (78) | L | `IsNeverZero.imax_eq_max` VLevel.lean:111 (`b+1 ≠ 0`) |
| `limax_self` (79) | L | `imax_self` VLevel.lean:101 |
| `limax_max` (80) | L | cases: `b=c=0` gives 0 = max 0 0. `b=0,c≠0` gives `max a c = max 0 (max a c)`. Symmetric case is the same. Both ≠0 gives `max a (max b c)` = `max (max a b) (max a c)` |
| `limax_imax` (82) | L | cases: `c=0` gives `imax a 0 = 0 = max 0 0`. `c≠0` gives `imax b c = max b c ≠ 0`, so LHS = `max a (max b c)` = RHS `max (max a c) (max b c)` |

### Expressions: `closed` (`ClosedN`, VExpr.lean:99-104)

| axiom | verdict | justification |
|---|---|---|
| `closed_bvar` (101) | T | `ClosedN (bvar i) k ↔ i < k` (`lt i k` = `i+1 ≤ k`) |
| `closed_srt` (102) | T | `True` |
| `closed_app` (103) | T | conjunction |
| `closed_lam` (105) | T | body at `k+1` |
| `closed_pi` (107) | T | body at `k+1` |

### `lift n k e e2` ≡ `e2 = liftN n e k` (VExpr.lean:17, 38-44)

| axiom | verdict | justification |
|---|---|---|
| `lift_bvar_lt` (112) | T | `liftVar n i k = i` if `i < k` (VExpr.lean:17, 19) |
| `lift_bvar_ge` (113) | T | `k ≤ i → liftVar = n + i`. `add i n j` is `j = i+n`, the same value (`liftVar_le` :20) |
| `lift_srt` (115) | T | :40 |
| `lift_app` (116) | T | :42 |
| `lift_lam` (118) | T | :43, body at `k+1` |
| `lift_pi` (120) | T | :44 |
| `lift_closed` (123) | A | `ClosedN.liftN_eq (self : ClosedN e k) (h : k ≤ j) : liftN n e j = e` (VExpr.lean:117). The spec's `j,k` are Lean's `k,j`. The hypotheses match exactly, `n` is arbitrary |

### `inst k e a e2` ≡ `e2 = inst e a k` (VExpr.lean:187-188, 240-246)

| axiom | verdict | justification |
|---|---|---|
| `inst_bvar_lt` (128) | T | `instVar i e k = bvar i` if `i < k` |
| `inst_bvar_eq` (129) | T | `i = k` gives `liftN k e` (= `liftN k e 0`), matching `lift k z a a2` |
| `inst_bvar_gt` (130) | T | index `i+1` with `k ≤ i` means `i+1 > k`, so the result is `bvar ((i+1)-1) = bvar i`. The three bvar cases are exhaustive and disjoint |
| `inst_srt` (132) | T | :242 |
| `inst_app` (133) | T | :244 |
| `inst_lam` (135) | T | :245, body at `k+1` |
| `inst_pi` (137) | T | :246 |
| `inst_closed` (140) | A | `ClosedN.instN_eq (self : ClosedN e1 k) (h : k ≤ j) : e1.inst e2 j = e1` (VExpr.lean:482). Same hypotheses. The lift-by-`k` in `inst_bvar_eq` never fires: under `d` binders the loose indices are `< j+d ≤ k+d`, so `bvar (k+d)` never occurs. Sanity check `build/audit/probe.auf` (`inst_closed_ex`, verified) |

### Contexts (Typing/Basic.lean:6-8)

| axiom | verdict | justification |
|---|---|---|
| `lookup_z` (154) | T | `Lookup (ty::Γ) 0 ty.lift`, where `lift = liftN 1 · 0` gives `lift (s z) z` |
| `lookup_s` (156) | T | `Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift`. The head is the innermost binder, as in Lean4Lean |

### Judgment (IsDefEq, Typing/Basic.lean:18-56)

| axiom | verdict | justification |
|---|---|---|
| `ty` (166, def) | D | `HasType` = diagonal (Basic.lean:60) |
| `bvar` (168) | T | :19 |
| `symm` (170) | T | :20 |
| `trans` (172) | T | :21, same type `A` on both premises |
| `sortDF` (174) | T, WF dropped | :22-24. The result type is `sort (succ l)` with the **left** `l`, as in Lean4Lean. Dropping WF is sound (§1) |
| `appDF` (176) | T | :32-35. The result is `B.inst a` with the **left** argument `a`. `inst z B a R` is `R = inst B a 0` ✓ |
| `lamDF` (179) | T | :36-39. The body context is `A::Γ` with the **left** `A`, and the result is `forallE A B` (left `A`) ✓ |
| `forallEDF` (182) | T | :40-43. Body context `A::Γ` (left), result `sort (imax u v)` ✓ |
| `defeqDF` (185) | T | :44 |
| `beta` (187) | T | :45-47. Premises `A::Γ ⊢ e : B` and `Γ ⊢ a : A`. The result is `e.inst a : B.inst a`, both at `k=0` ✓ |
| `eta` (190) | T | :48-50. `e.lift = liftN 1 e 0` is `lift (s z) z e e1` ✓. The binder type `A` of the λ is the one in `forallE A B` ✓ |
| `proofIrrel` (193) | T | :51-53 (`sort .zero` = `srt lz`) |
| (`constDF`, `extra`) | omitted | replaced by per-constant generated axioms and MM0 `def` unfolding (§10); not audited here |
| `inh_i` (204) | sound, by definition | `inh` has this single introduction rule, so `inh G A` holds iff `∃ e. G ⊢ e : A`. The witness is built from the theorem's own variables (no dummies), which is fine for a closed Lean proof term |

## 3. Issues, ranked

### 1. (Medium, completeness) `leqv` cannot derive valid laws that nanoda accepts

Nanoda decides `≤` with **case splits on params under `imax`** (`refs/nanoda_lib/src/level.rs:160`
`leq_imax_by_cases`, used at :189 and :191), so it is complete for `≈`. The spec's equational
set is not. `build/audit/levelmodels2.py` searches finite algebras `(D, 0, s, max, imax)` that
satisfy every `leqv` axiom as an identity. It found 4-element countermodels for these
**valid** laws, which are therefore **not derivable** from the spec:

* `max u (imax u v) ≈ max u v`
* `imax u (max u v) ≈ max u v`
* `imax (imax u v) v ≈ imax u v`
* `imax (max u w) v ≈ max (imax u v) (imax w v)`, i.e. right distributivity, which is missing
* `max (imax u v) (imax v u) ≈ max u v`

(`max (imax u v) v ≈ imax u v` *is* derivable, via `limax_imax` and `limax_self`; see
`build/audit/probe.auf`, verified.) So any Lean term whose checking needs one of these, for
example `Sort (max u (imax u v))` against `Sort (max u v)`, cannot be certified. Resolved later
by the case-split rules (§4).

The fix is not a soundness matter, and it is hard to state in MM0. A case-split rule
`l[u:=0] ≈ l'[u:=0] ∧ l[u:=succ u] ≈ l'[u:=succ u] → l ≈ l'` needs substitution of an MM0
*variable*, which can't be written first-order without DV conditions. Options:

* (a) Add the missing laws as more `L` axioms (right distributivity
  `imax (max a b) c ≈ max (imax a c) (imax b c)`, and absorption
  `max a (imax a b) ≈ max a b`), then re-run the countermodel search
  (`python3 -I build/audit/levelmodels2.py 4`, extended with the new axioms) on a list of
  nanoda-style goals until no countermodel remains. Each new law must still be checked by cases
  on `eval`.
* (b) Give the `leqv` layer explicit param indices (`lparam: nat > lvl`) with a syntax-directed
  `lsubst` relation, plus a case-split axiom. This costs the "instL is MM0 substitution" property.
* (c) Collect real failures from the elaborator first. Lean-generated levels may rarely need more
  than the current set plus right distributivity.

### 2. (Low, completeness) `constDF` for `def` constants with distinct-but-equivalent levels

For `term` constants, the generator emits `c_df` with a `leqv` premise (`spec/examples/consts.mm0`).
For `def` constants, `c u ≡ c u'` with `u ≈ u'` (and `u ≠ u'` syntactically) unfolds to
`body[u] ≡ body[u'] : T[u]`. That is admissible (`IsDefEq.instL_r`, Theory/Typing/Strong.lean:703)
but is not derivable in one step. The elaborator must replay the body's typing derivation,
using `sortDF`/`c_df` at the leaves, or the generator must emit a per-def proved lemma.
Nothing new needs to be trusted, but the work is real. Kernels hit this case when comparing
`f.{max u v}` with `f.{max v u}`.

### 3. (Low, a proof obligation on generated files, not on this file)

The shortcuts are sound for this file's five constructors. Every later `term` of sort `expr`
must keep the model valid:

* `closed z (c us)` is valid only for constants without `expr` arguments. `.const` is
  `ClosedN`-trivially closed, `lit` is fine, and `proj` is not.
* Any `expr`-argument term (`proj`, §4.5) needs structural `closed_/lift_/inst_` axioms that
  recurse into its arguments. Without them `lift_closed`/`inst_closed` remain sound but useless
  for it, and the lift/inst relations become incomplete. A careless `closed k (proj i e)`
  without a premise on `e` would be **unsound**.

### 4. (Info/doc)

* The header (lines 6-10) says each `term` constant gets a generated `constDF` axiom. It should
  also say that it gets a `closed z` axiom (as in `consts.mm0`), and that this is valid only
  because the constant has no `expr` arguments.
* The `leqv` doc comment (lines 56-60) calls it "semantic equivalence". `leqv` is the derivable
  sub-relation of `≈`, so "sound approximation of `≈`" would be more precise. The comment
  already says "not known to be complete". Issue 1 shows it is incomplete.
* `inh nil T` does not itself say that `T` is a type. That follows from
  `IsDefEq.isType` (Typing/Lemmas.lean:873), which needs `env.Ordered`, so it is part of the env
  adequacy argument of §10. If statement readers should not depend on that, statements
  could also include `ty nil T (srt u)`.

### Checked and fine (the explicit questions)

* **Off-by-one.** `le/lt/add` conventions, `lift_bvar_ge` (`j = i+n`), `inst_bvar_gt`
  (`bvar (s i) ↦ bvar i` when `k ≤ i`) and the `s k` under binders in `closed/lift/inst_{lam,pi}`
  all match Lean4Lean.
* **Argument order.** Every use matches its definition: `inst z B a R`, `inst z e a r`,
  `lift (s z) z e e1`, `lift k z a a2`, `lift (s z) z A A2`, and `lift_closed`/`inst_closed`
  with `(closed j, j ≤ k) ⇒ op at k`.
* **Annotation side.** Every rule uses the left-hand annotation, exactly as in Lean4Lean.
* **WF drop, `inh_i`, non-functionality, hypothesis-only variables.** All sound (§1).

## 4. Level case splits and the generated per-declaration axioms (argued here, to be re-audited)

### Level case splits (`spec/lean.mm0`, after the `leqv` axioms)

Semantics as before: `leqv l r` means `l` and `r` have equal values under every assignment of
the level variables, and `lparam n` is one more level variable (index `n` in a separate
namespace from the MM0 variables).

| axiom | argument |
|---|---|
| `lnth_*`, `linst_*`, `lsubst_*` | Defining clauses of syntax-directed relations on level syntax. `lsubst_lt`/`lsubst_gt` need `m ≠ n`, given by `lt`. There are no clauses for MM0 variables, so `linst`/`lsubst` can only be proved for levels built from `lz/ls/lmax/limax/lparam`. Soundness does not depend on that. |
| `leqv_cases` | Fix an assignment ρ. If ρ(n) = 0, then `l` takes the value of `l[n:=0]`, and likewise `r`, so they agree by the first premise. If ρ(n) = m+1, let ρ' = ρ[n:=m]; then `l[n := ls (lparam n)]` at ρ' is `l` at ρ, likewise for `r`, so they agree by the second premise. (The substitution lemma for level syntax is a simple induction; `lsubst` replaces only occurrences in `l`, not inside the substituted level.) |
| `leqv_inst` | `l2` and `r2` are `l` and `r` under the substitution `lparam i ↦ S[i]`. Their values at ρ are those of `l` and `r` at the assignment that sends `lparam i` to the value of `S[i]` at ρ. Those agree by the premise. |

Completeness (not needed for soundness): after abstracting the variables, splitting on every
parameter that occurs as the second argument of an `imax` leaves `imax`-free goals, which the
normal form decides.

### Generated per-declaration axioms (stage A, `lean0/src/gen.rs`)

These live in the generated `.mm0`, not in `lean.mm0`, and must be read against the Lean
declaration. They are trusted in the same sense that nanoda trusts the export's recursors (which
it re-derives and compares). Nothing trusted does that reading: the instances come from the export
and nanoda, and nothing trusted checks that a declaration is legal (strict positivity,
uniform parameters, field universes, the elimination level) or that its recursor is the one
the declaration determines. So the arguments below hold per kind of axiom, *assuming* the
declaration is legal and the export's recursor is the right one. This is the largest gap in
the trusted base; a spec-level schema of inductive well-formedness (stage B, planned) is to remove it.

| axiom class | Lean4Lean counterpart / argument |
|---|---|
| `c_df` (axioms, inductive types, constructors, recursors, quotient primitives, opaques) | `constDF` for a constant whose type is the given `T` (`T` is checked well-typed by the public theorem `c_wf`) |
| `c_closed`: `closed k (c us)` for every `k` | constants have no loose bound variables (`ClosedN` of `.const`) |
| `R_c` (def) + `R_c_iota`: `ty G LHS T > deq G LHS (R_c ps ms mins fs) T` | The iota rule of the exported recursor rule: `rec ps ms mins is (c cps fs) ≡ val ps ms mins fs` whenever the left side is well-typed. The constructor's parameters, levels and the indices are separate variables, as in nanoda's `reduce_rec`. They are forced to agree with the recursor's by the typing premise (typing makes the major's type defeq to `I ps is`, and inductive type formers are injective in the model). |
| `S_proj` with `_closed`, `_lift`, `_inst` | A projection is structural for these relations, exactly as `.proj` would be in `VExpr`. |
| `S_proj_i_df` | Typing of `e.i` for `e : S us ps`: the field type with parameters and earlier projections substituted (the `inst` premises do this outermost-first, which is simultaneous substitution). The premise `leqv (lmax (ls lz) L) L` (sort at least 1) is present unless every field up to `i` is a proposition, matching nanoda's `infer_proj` restriction for structures that may be propositions. |
| `S_proj_i_dfp` | The same typing, for projecting from a structure that is a proposition: premises `leqv L_j lz` for every field `j ≤ i` that is not a proposition at all levels (`L_j` the level of field `j`'s sort). Generated only when each such `L_j` can be zero, which in Init means `Exists` and `Nonempty` (`h.1 : P` for `h : ∃ x : P, Q x`, with `P : Prop`). Sound: with every field up to `i` a proposition, `e.0, …, e.i` are definable by eliminating `e` into `Prop`, which is allowed for every inductive proposition, and the field types agree by proof irrelevance. nanoda's `infer_proj` (like Lean's kernel) requires only the fields that the projected one depends on to be propositions; requiring all of them up to `i` is stronger, so this is no more permissive. |
| `S_proj_i_mk` | `(S.mk ps fs).i ≡ fs[i]` when well-typed (nanoda's `reduce_proj`). |
| `S_eta` | Structure eta for non-recursive structures (one constructor, no indices): `e ≡ S.mk ps (e.0) … (e.n)` at `S us ps`. Unit eta and nanoda's iota-on-structure expansion are derived from it. |
| `Quot_lift_mk`, `Quot_ind_mk` | `Quot.lift f h (Quot.mk r a) ≡ f a` and `Quot.ind f (Quot.mk r a) ≡ f a` when well-typed (Lean4Lean's quotient `extra` rules). |

K-like reduction (`Eq.rec` on a non-constructor) has no axiom: the major premise is replaced by
the constructor using `proofIrrel`.

## 5. Nat literals (argued here, to be re-audited)

### Binary numerals and arithmetic (`spec/lean.mm0`, "Nat literals")

Model: a `bin` term denotes a natural number, with `b0 ↦ 0`, `bd0 n ↦ 2n` and `bd1 n ↦ 2n+1`.
Each relation denotes the graph of its operation: `bsucc a b` is `a+1 = b`, `bdbl a b` is
`2a = b`, `badd a b c` is `a+b = c`, `baddc a b c` is `a+b+1 = c`, `bmul` is `·`, `bpow` is `^`
(with `0^0 = 1`, as Lean's `Nat.pow`), and `band`/`bor`/`bxor` are bitwise and, or and exclusive
or. Every axiom is then an arithmetic identity on values, true for all numerals, canonical or
not (`bd0 b0` also denotes 0). So a non-canonical numeral can never prove a false fact.

| axioms | check (values; `a' = 2a` or `2a+1` by the outer constructor) |
|---|---|
| `bsucc_0/d0/d1` | `0+1 = 1`; `2a+1 = 2a+1`; `a+1 = b ⇒ (2a+1)+1 = 2b` |
| `bdbl_0/d0/d1` | `2·0 = 0`; `2·(2a) = 2(2a)`; `2·(2a+1) = 2(2a+1)` |
| `badd_0l/0r` | `0+b = b`, `a+0 = a` |
| `badd_00/01/10/11` | `2a+2b = 2c`; `2a+(2b+1) = 2c+1`; `(2a+1)+2b = 2c+1`; `(2a+1)+(2b+1) = 2(a+b+1)` with `c = a+b+1` |
| `baddc_0l/0r` | `0+b+1 = c` from `b+1 = c`; symmetric |
| `baddc_00/01/10/11` | `2a+2b+1 = 2c+1`; `2a+(2b+1)+1 = 2(a+b+1)`; symmetric; `(2a+1)+(2b+1)+1 = 2(a+b+1)+1` |
| `bmul_0/d0/d1` | `a·0 = 0`; `a·2b = 2(ab)`; `a(2b+1) = 2(ab) + a` |
| `bpow_0/d0/d1` | `a^0 = 1`; `a^(2b) = (a^b)²`; `a^(2b+1) = (a^b)²·a` |
| `band_*`, `bor_*`, `bxor_*` | bit by bit: the low bit of the result is the operation on the low bits, and the rest is the operation on `⌊a/2⌋`, `⌊b/2⌋` (`2c` written `bdbl c d` where it may be 0) |

The relations are functional in the model, so overlapping clauses (e.g. `badd_0l`/`badd_0r` on
`0+0`) always agree. Lean0's prover (`mm0kit/src/bin.rs`) only builds canonical numerals.

### `lit` (`spec/lean.mm0`)

`lit n` denotes `Nat.succ^n Nat.zero` (as `VExpr` constants of the environment), which is how
Lean4Lean translates a Nat literal (`Literal.toConstructor`, unfolded). `closed_lit` holds
because constants have no loose bound variables. In an environment without `Nat.zero` and
`Nat.succ` no literal axioms are generated, and `lit` is inert.

### Generated literal axioms (`lean0/src/natlit.rs`)

| axiom | argument |
|---|---|
| `Nat_lit_zero`: `deq G (lit b0) Nat.zero Nat` | in the model, `Nat.zero ≡ Nat.zero : Nat` (`constDF`). Generated only when `Nat.zero : Nat` |
| `Nat_lit_succ`: `bsucc a b > deq G (lit b) (Nat.succ (lit a)) Nat` | both sides denote the same term `succ^(a+1) zero`, which has type `Nat` because `Nat.succ : Nat → Nat` (checked by the generator) |
| `Nat_add_lit`, `Nat_sub_lit`/`_lit0`, `Nat_mul_lit`, `Nat_div_lit`/`_lit0`, `Nat_mod_lit`/`_lit0`, `Nat_gcd_lit`/`_lit2`, `Nat_beq_lit`/`_lit_lt`/`_lit_gt`, `Nat_ble_lit`/`_lit_gt`, `Nat_land_lit`, `Nat_lor_lit`, `Nat_xor_lit`, `Nat_pow_lit`, `Nat_shiftLeft_lit`, `Nat_shiftRight_lit` | `op (succ^a zero) (succ^b zero) ≡ succ^(f a b) zero : Nat` (or `≡ Bool.true/false : Bool`), where the premises force the value: `sub` from `c+b = a` or `a+c = b`; `div`/`mod` from `q·b = m`, `m+r = a`, `r+x+1 = b` (so `r < b`, Euclidean division, and `b = 0` has its own axiom: `a/0 = 0`, `a%0 = a`); `gcd` from `g·p = a`, `g·q = b` (`g` divides both) and `x·a = y·b + g` or `y·b = x·a + g` (every common divisor divides `g`, so `g = gcd a b`; `a = b = 0` forces `g = 0`); `beq` false from `a+c+1 = b` or `b+c+1 = a`; `ble` from `a+c = b` / `b+c+1 = a`; shifts via `2^b`. |

**Trust gap (stage A).** The operation axioms are valid only if the environment's definition
of each operation computes it on numerals, which is Lean4Lean's `HasPrimitives` invariant.
Lean4Lean establishes it by checking defining equations when the definition is added
(`Primitive.lean`: e.g. `Nat.add x 0 ≡ x` and `Nat.add x (succ y) ≡ succ (Nat.add x y)` for
fresh `x y`; well-founded unfolding for `gcd`, `div`, `mod` and the bitwise operations). Lean0,
like nanoda and the C++ kernel, only checks the name and the type (`Nat → Nat → Nat`, or
`→ Bool` for `beq`/`ble`). Planned stage B: prove Lean4Lean's equations as theorems in the
certificate, and state each axiom with them as premises.

String literals have no axioms: a string literal is translated as its expansion
`String.ofList [Char.ofNat n, …]` (Lean4Lean's translation; nanoda expands it in `def_eq`), so
every step about one is an ordinary derivation.

## 6. Substitution and weakening (argued here, to be re-audited)

### `cinst` (`spec/lean.mm0`, after `lookup`)

| MM0 | interpreted as |
|---|---|
| `cinst k G0 A0 a G1 G` | `Ctx.InstN G0 a A0 k G1 G` (Typing/Lemmas.lean:86) |

`cinst_z` and `cinst_s` are its two constructors, transcribed: `zero : Ctx.InstN 0 (A₀ :: Γ₀)
Γ₀` and `succ : Ctx.InstN k Γ Γ' → Ctx.InstN (k+1) (A::Γ) (A.inst e₀ k :: Γ')`, with the
`inst` relation for `A.inst e₀ k`. Context entries are types relative to their tail, as in
Lean4Lean's list contexts (`Lookup` lifts on the way out), so the substitution depth of the
entry `k` places above `A₀` is `k`, as in the constructor. `Γ₀`, `e₀` and `A₀` are arguments
of the MM0 relation where Lean4Lean has them as parameters of the inductive.

### `instDF` (`spec/lean.mm0`, "Admissible rules")

`deq G0 a a A0 > cinst k G0 A0 a G1 G > deq G1 e e2 A > inst k e a r > inst k e2 a r2 >
inst k A a R > deq G r r2 R` is `IsDefEq.instN` (Typing/Lemmas.lean:634): from
`henv : env.Ordered`, `h₀ : env.HasType U Γ₀ e₀ A₀`, `W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ` and
`H : env.IsDefEq U Γ₁ e1 e2 A` it concludes `env.IsDefEq U Γ (e1.inst e₀ k) (e2.inst e₀ k)
(A.inst e₀ k)`. The `inst` premises pin `r`, `r2`, `R` to those terms (functionality, §1).

The rule is valid in the standard model of §1, which is all the soundness argument of §1
needs. In particular it need not be checked against the generated axioms: those are claims
about `IsDefEq` of the translated environment (§4, §5), not extra rules of the model, so
`instN` covers every derivation regardless of which axioms produced its premises. The one
assumption is `env.Ordered` for the translated environment (every constant's type and every
defeq rule well-typed in the earlier environment), which holds because the environment was
checked; the stage-A axioms already rest on the same reading of the environment.

`U` is the theorem's level-variable count, as for the other rules (§1, WF conditions).

### `cext` (`spec/lean.mm0`, after `cinst`)

| MM0 | interpreted as |
|---|---|
| `cext n G G2` | `Ctx.LiftN n 0 G G2` (Typing/Lemmas.lean:8-10) |

Only the `zero` constructor, `Ctx.LiftN n 0 Γ (As ++ Γ)` with `As.length = n`: `cext_z` and
`cext_s` build `As ++ Γ` one entry at a time, counting `n`. Every derivable `cext n G G2` has
`G2` equal to `G` with `n` entries (any expressions) consed on, which is the constructor's
instance with `As` those entries; `Ctx.LiftN.zero` puts no condition on `As`.

### `weakDF` (`spec/lean.mm0`, "Admissible rules")

`deq G e e2 A > cext n G G2 > lift n z e r > lift n z e2 r2 > lift n z A R > deq G2 r r2 R` is
`IsDefEq.weakN` (Typing/Lemmas.lean:501) for `W : Ctx.LiftN n 0 Γ Γ'`: from `henv :
env.Ordered` and `H : env.IsDefEq U Γ e1 e2 A` it concludes `env.IsDefEq U Γ' (e1.liftN n)
(e2.liftN n) (A.liftN n)`. The `lift` premises pin `r`, `r2`, `R` (functionality, §1). The
argument is the one for `instDF`: the rule is valid in the standard model, so it needs no check
against the generated axioms, and its one assumption, `env.Ordered`, is the one `instDF` and
the stage-A axioms already rest on. The generated rules are all schematic in `G` (a context
appears only as the variable `G` of their premises and conclusion), as the model's constant
rules are, so nothing in them depends on the context's length.


## 7. Multi-part certificates (argued here, to be re-audited)

An export too large for one MMB file (its table data must stay under 4 GiB) is certified in
parts (`lean0 gen --parts P`): part `K` certifies a consecutive range of declarations. The
text it is verified against is built by the trusted side, `lean0 joined NAME.part0.mm0 ...
NAME.partK.mm0` (`lean0-check/src/joined.rs`), from the parts' statement files alone: the
spec, then the statements of parts `0..K-1` (each part's `NAME.partJ.mm0` after its two
header lines) with two textual rewrites, then part `K`'s own statements.
`scripts/check-parts.sh` runs it and both verifiers for every part. The rewrites are:

* `theorem` becomes `axiom`. Part `J < K` proves the theorem, against a joined file that is a
  prefix of part `K`'s (up to these same rewrites), so the axiom is valid in every model of
  that prefix in which part `J`'s abstract definitions mean what part `J`'s MMB defines them as.
* An abstract `def c (us): expr;` (a Lean theorem's proof term, whose body is only in the
  MMB) becomes `term c (us): expr;`. Part `K` then proves its theorems for every value of
  `c`, in particular for the body part `J` gave it, so the parts' results hold together in
  the one model where each `c` has its body. (Had part `K` restated the def with a body of its
  own in its MMB, nothing would tie that body to part `J`'s; making it a plain term avoids
  the question.) Definitions with public bodies are restated as they are, so their bodies are
  compared as text.

So the parts compose: every statement of every part holds in the standard model extended by
the definitions of all parts, given the spec's axioms and each part's generated stage-A
axioms. The trusted addition is the two line-by-line rewrites (`joined.rs`, about 20 lines
of code). Generated names are the same in every part (lemmas made while proving have
the reserved prefix `lean0_` and never appear in a `.mm0`), and a definition's closedness
theorem `c_closed` is a public theorem so that later parts can restate it; the generator does
not need to be trusted for any of this, since a mismatch fails a verifier. A single-file
certificate is the case `K = 0`: `lean0 joined NAME.mm0` is the spec followed by its
statements. (Until 2026-10-30 the generator wrote that text itself, as `NAME.joined.mm0`,
and `scripts/certify.sh` verified against it unchecked, so a generator that weakened the spec
there would have passed. The generator no longer writes it, except for tamper tests.)

**A part without a certificate** (2026-10-31, all of Std). A part's statements can be written
without its proofs (`lean0 gen --statements-only`, for a declaration that alone passes the MMB
format's 4 GiB of table data). Such a part has a `.mm0` and no `.mmb`. `lean0 joined` restates
its statements for the later parts like any other part's, so its theorems become axioms that
nothing proves. That is an explicit, named gap of the same kind as a generated axiom: the
claim for that declaration rests on nanoda (which checked it) and not on a verifier. `lean0
check` still compares its statements with the export, so they say what Lean's declaration
says. A report of a multi-part run must list such parts. In Std's certificate there is one:
`goCache_Inv_of_Inv._mutual`, `std.part53bbbb.mm0`.

## 8. From the certificate to Lean: the statement checker

The verifiers establish that the certificate proves its `.mm0` statements. What ties those
statements to the Lean declarations is `lean0 check EXPORT STATEMENTS.mm0...`
(`lean0-check/src/statements.rs`, about 470 lines with comments; the `lean0-check` crate does
not depend on the generator), written independently of the generator: it
uses only nanoda's export parser and expression type, and parses the generated `.mm0` text
itself, accepting only the forms lean0 writes. For every declaration of the export it checks:

* exactly one MM0 term claims to stand for it (the doc comment "Lean ... `NAME`"), taking one
  level variable per universe parameter, and no term claims a constant the export lacks;
* every statement giving that term's type, `ty G (c us) T` or the `constDF` axiom
  `deq G (c us) (c us2) T`, has `T` equal to the declaration's type, read back into Lean (de
  Bruijn indices, sorts and levels, constants with their levels, projections by structure and
  index, Nat literals; binder names and styles are not compared; a `let` is inlined and a
  string literal expanded, as the translation does);
* a theorem's and a definition's type is stated by a proved theorem, not an axiom;
* a definition's body is its value.

Not checked by it: the generated axioms (inductive, quotient and literal rules, §4 and §5),
which are argued and generated, not compared with anything in the export; and whether a
theorem's proof term (an abstract def) is the export's (it is never stated, so it cannot
matter). The comparison reads both sides structurally, so a translation bug, a doc comment
naming the wrong constant, or a statement edited by hand is reported, with the first place
the two differ. All of Init (59,423 declarations, 186,932 statements, the 32 parts' own
`.mm0` files) passes in 13 s; `scripts/test.sh` checks that edited statements are rejected.

After the check, `lean0 check` lists the export's top-level declarations (theorems,
definitions, opaques and axioms that no declaration of the export mentions; for a slice
`lean4export MOD -- NAMES`, the named ones) with their Lean types, from nanoda's pretty
printer (`lean0-check/src/summary.rs`). The list is for the person reading the result and
plays no part in the check: what is checked is every declaration, as above.

## 9. Notations in the spec (2026-10-30)

`spec/lean.mm0` declares notations, and its formulas are written with them: `⊢ G, e ≡ e2 : A`
for `deq G e e2 A`, `⊩ G, e : A` for `ty G e A` (used by no formula of the spec itself, which
states typing premises as `deq`, as Lean4Lean does), `λ A. e` and `Π A. B` for `lam` and `pi`,
`f @ a` for `app`, `# i` for `bvar`, `A :: G` and `[]` for `cons` and `nil`, `a ⊔ b` for
`lmax`, and `≤`, `<` and `≈` for `le`, `lt` and `leqv`. Each has an ASCII form as well,
declared first (`|- G, e == e2 : A`, `||- G, e : A`, `\ A. e`, `\Pi A. B`, `\/`, `<=`, `~=`);
the Unicode form is declared last. The delimiters are `( ) , .`.
How a formula parses is fixed by MM0 (`mm0.md`, "Notations"), and the verifiers parse the
spec themselves, so a reader has to read each formula through the declarations at the
terms; the precedences make `λ` and `Π` extend as far right as possible, and `@` bind
tighter than `::`, which binds tighter than the judgment's separators; `⊔` (65) binds
tighter than `≈` (50), and applications such as `ls a` tighter than either.

The rewrite from prefix form was checked to state exactly the same statements:

* every certificate made with the old, prefix spec (the ten in `build/gen/` at the time:
  `core`, `induct`, `lit`, `initsample`, `congtype`, `deflevels`, `handlecycle`,
  `projhandle`, `propproj`, `weakhandle`) verifies with both verifiers against the new text
  followed by its statements. An MMB restates every statement of the spec, and a verifier
  compares each with its own parse of the text, so both verifiers read every formula of the
  new spec as the old one;
* the generator's parser (`mm0kit/src/parse.rs`, untrusted) reads the new spec as the old:
  `lean0 gen --spec` with the new text writes byte-identical `.mmb` files.

Both checks were run again when `⊔` and `⊩` were added, and a generated statement rewritten
with `⊩` and `⊔` (and in ASCII) verified as the original, while one with two arguments
swapped was rejected.

The generated statements keep the prefix form (`deq G e e2 A`), which MM0 allows for every
term with or without a notation; the statement checker reads only that form. No notation
token looks like an identifier (`[a-zA-Z_][a-zA-Z0-9_]*`), so none can collide with a
generated name.

## 10. The encoding: how the spec departs from Lean4Lean's presentation

The spec transcribes Lean4Lean's `IsDefEq` rules over de Bruijn terms (`VExpr`) as closed
first-order MM0 terms: sorts `nat` (indices), `lvl`, `expr` and `ctx`; the judgment
`deq G e e2 A` (`⊢ G, e ≡ e2 : A`); and the side relations `lift`, `inst`, `lookup` and
`closed`, with one axiom per defining clause, which the generator proves syntax-directed. The
departures from the verbatim presentation:

* **No environment term.** Lean4Lean's `VEnv`, with the `constDF` and `extra` rules, is
  replaced by one MM0 declaration per Lean constant, whose arguments are the constant's
  universe parameters as `lvl` variables. A definition or theorem `c.{u v} : T := v` becomes
  `def c (u v: lvl): expr = $ v $;` with a proved typing theorem `⊩ G, c u v : T`, schematic in
  `G`; so δ-unfolding is MM0 unfolding, and universe instantiation (`instL`) is MM0
  substitution of the `lvl` variables. A theorem's body is abstract (only in the MMB), so the
  `.mm0` never shows a proof term. Axioms, opaques, inductive types, constructors, recursors and
  `Quot.*` become `term c (u v: lvl): expr;` with two generated axioms each: a `constDF` instance
  (`deq G (c us) (c us2) T` under `leqv` premises on the levels) and `closed k (c us)`.
  Soundness: an environment whose definitions are inlined proves the same judgments as the
  original (this is Lean4Lean's `extra` treatment of `c ≡ value : T`). That adequacy argument is
  on paper; a Lean proof over Lean4Lean's `VEnv` would close it.
* **Level variables are MM0 variables**, so `U` and `l.WF` disappear and every level axiom must
  hold schematically (§2). With the case-split rules of §4 (`lparam`, `leqv_cases`,
  `leqv_inst`) the axioms decide `leqv` completely: `imax`-free levels are compared by normal
  form, and a parameter under `imax` is split on until none is left.
* **Nat literals** (§5): `lit : bin > expr` over binary numerals, with generated axioms tying
  `lit` to `Nat.zero` and `Nat.succ` and to each accelerated operation. A **string literal** is
  translated as its `String.ofList` expansion and needs no axiom.
* **Projections and structure eta** (§4): one projection term per structure with generated
  typing and reduction axioms, rather than a single primitive `proj`, so that two structures'
  axioms never apply to the same term; eta as one axiom per non-recursive structure.
* **Inductives** (§4, stage A): the types, constructors and recursors are opaque constants as
  above, and each recursor rule is a generated schematic iota axiom
  `ty G LHS T > deq G LHS RHS T`, with the exported rule value as a public `def`. Nothing in the
  spec states inductive well-formedness; a spec-level schema from which the per-block axioms are
  derived (stage B) is planned.
* **`let`** is inlined during translation (derivations memoized on the DAG), and `mdata` is
  erased. Binder names and styles are not represented.

The generated `.mm0` therefore contains, per declaration, its `def` or `term`, its typing
statement, and for opaque constants the two generated axioms, plus the per-structure and
per-recursor axioms above; lemmas made while proving are local to the MMB. §8 says how those
statements are tied back to the export.
