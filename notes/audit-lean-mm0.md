# Audit: `spec/lean.mm0` against Lean4Lean (@ 67f63b0)

Scope: every axiom in `spec/lean.mm0`, which is four files (`lean-core.mm0`, and the
extensions `lean-ind.mm0`, `lean-quot.mm0`, `lean-lit.mm0` for inductive types, quotients and
Nat literals; a section named below is in the file of its subject, and `lean0 spec` prints
the four as one text). §1–3 audit the core rules (the judgment, the levels,
`lift`/`inst`/`closed` and the contexts; the spec's first 204 lines at the time); §4–8 argue
the additions since, §9 the notations, and §10 describes how the encoding departs from
Lean4Lean's presentation and the division of each file into three parts (syntax; definitions over
the judgment; the rules), with `lean0 modes` as the mechanical check that the first two parts
are definitions (§4, *Functionality*). Lean4Lean paths are relative to
`refs/lean4lean/Lean4Lean/` (`scripts/fetch-refs.sh`). The model-search scripts mentioned
below (`build/audit/`) are not part of the repository.

**What is proved and what is argued (2026-11-26).** This document was written before the
model existed, and its sections argue two things at once. The two now have different standing.

*Soundness* is no longer argued here: it is proved. Every rule of the spec is a theorem of
Tarski–Grothendieck set theory about a model defined there (`spec/tg`, described in §11; the
headline statements are in `spec/tg/results.mm0`), checked by both verifiers: the level rules
in `model-levels`, the core rules in `model-den` and `model-core`, the inductive schema in
`model-fold`, `model-nst` and `model-ci`, the quotients and the three standard axioms in
`model-quot`, the literals in `model-lit`, and the assembly with the spec's own statements
in `model-top`. Where a section below says a rule "holds in the model" or "is sound
because", read it as an explanation of that theorem, not as the evidence for it. The
informal standard model of §1 and the model sketch of §4 are kept as the reading that
guided the design.

*Correspondence with Lean* is still argued here, and only here: that each relation of the
spec says what the kernel computes or checks (the per-axiom tables of §2, §4, §5, with
Lean4Lean and the C++ kernel cited by function), and that a certificate's statements say
what the export's declarations say (§8). The model does not prove this. A spec that was
sound but stricter or differently shaped than Lean would still have a model. The evidence
is the tables, the comparison of every recursor type and rule with the kernel's on every
block (§4), `lean0 modes` (§4, *Functionality*), the negative tests, and the size of the
certified corpus.

What is trusted without proof, then: the set theory `tg.mm0` (77 axioms; choice as an
operator, §4); the encoding of the spec's syntax as sets (53 axioms, §11); the reading of the
spec as Lean's type theory (the tables); the statement checker (§8) and the restating of
earlier parts (§7); and, for a development with axioms of its own, those axioms.

Known departures from Lean4Lean's judgment: substitution and weakening are rules (§6), the
literal operations are rules over provable characterizations (§5, slightly stronger than
Lean's definitional equality in principle), and the level rules are complete where the
kernel's procedure is not (§3, §4).

## 1. Soundness argument (why a per-axiom check is enough)

(Superseded as evidence of soundness by the model of §11; kept as the reading of each sort and
relation against Lean4Lean that the tables of §2 use.)

Every axiom in the file is a Horn clause over closed first-order terms. `wff` has no
connectives, there is no negation, and no sort admits bound or dummy variables (`strict`,
`mm0.md:82`). So an MM0 derivation is a finite tree of schematic axiom instances, and the
system is sound for the intended reading if every axiom is valid in this **standard model**:

| MM0 | interpreted as |
|---|---|
| `nat` terms `nz`, `s` | `Nat` |
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
* **WF conditions.** Lean4Lean needs `l.WF U` only in `sort_df`, `constDF` and `extra`. Because
  `lvl` is `strict` (no dummies), every level term in a proof of a theorem with level variables
  `u₀ … uₙ₋₁` is built from those variables and `lz/ls/lmax/limax`. Map `uᵢ ↦ .param i` and take
  `U = n`. Then every level in the derivation satisfies `WF n`, and the dropped premises hold.
  Using a lemma at an instance (MM0 substitution of `lvl` variables) is justified by
  `IsDefEq.instL` (Typing/Lemmas.lean:595). If the proof uses a level variable that the
  statement does not need, instantiate it with `lz`. All the `leqv` laws are identities of
  `eval`, so they survive substitution of arbitrary `VLevel`s for their metavariables.
* **Variables that occur only in hypotheses** (`u` in `lam_df`/`conv`, `A B` in `app_df`, `e2`
  in `deq_trans`, `j` in `*_closed`, `B` in `lookup_s`, `B` in `beta`). In MM0 the proof supplies
  every axiom argument explicitly, and every sort is inhabited (`nz`, `lz`, `srt lz`, `nil`). So
  this is just ordinary Horn-clause instantiation: no pitfall.
* (Until 2026-11-26 the rule `bvar_ty` was named `bvar`, like the term.) Terms and theorems live in separate namespaces,
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
| `limax_succ` (78) | L | `IsNeverZero.imax_eq_max` VLevel.lean:111 (`b+1 ≠ 0`) |

Until 2026-11-26 five more identities of `imax` were axioms: `limax_zero_l` (`imax 0 a = a`),
`limax_one` (`imax 1 a = a`), `limax_self` (`imax a a = a`), `limax_max` (`imax a (max b c) =
max (imax a b) (imax a c)`) and `limax_imax` (`imax a (imax b c) = max (imax a c) (imax b c)`).
Each follows from the two rules above by `leqv_cases` and `leqv_inst` (§4): state it at
parameters, split each parameter in a second argument of `imax` into zero and a successor, and
the cases are identities of `max`; then put arbitrary levels back. The generator proves the
ones a certificate uses as local lemmas at their first use (`mm0kit/src/level.rs`, `derive`;
`tests/lean/DefLevels.lean` exercises all five), so both verifiers check the derivations, and
`spec/lib.auf` has `limax_self` by hand. They are still theorems of the model
(`model-levels.mm0`), where other proofs use them.

### Expressions: `closed` (`ClosedN`, VExpr.lean:99-104)

| axiom | verdict | justification |
|---|---|---|
| `closed_bvar` (101) | T | `ClosedN (bvar i) k ↔ i < k` (`lt i k` = `i+1 ≤ k`) |
| `closed_srt` (102) | T | `True` |
| `closed_app` (103) | T | conjunction |
| `closed_lam` (105) | T | body at `k+1` |
| `closed_pi` (107) | T | body at `k+1` |
| `closed_cst` | T | `ClosedN (.const c ls) k ↔ True`: an opaque constant (`cst a ls`, §10) has no bound variables |

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
| `inst_bvar_eq` (129) | T | `i = k` gives `liftN k e` (= `liftN k e 0`), matching `lift k nz a a2` |
| `inst_bvar_gt` (130) | T | index `i+1` with `k ≤ i` means `i+1 > k`, so the result is `bvar ((i+1)-1) = bvar i`. The three bvar cases are exhaustive and disjoint |
| `inst_srt` (132) | T | :242 |
| `inst_app` (133) | T | :244 |
| `inst_lam` (135) | T | :245, body at `k+1` |
| `inst_pi` (137) | T | :246 |
| `inst_closed` (140) | A | `ClosedN.instN_eq (self : ClosedN e1 k) (h : k ≤ j) : e1.inst e2 j = e1` (VExpr.lean:482). Same hypotheses. The lift-by-`k` in `inst_bvar_eq` never fires: under `d` binders the loose indices are `< j+d ≤ k+d`, so `bvar (k+d)` never occurs. Sanity check `build/audit/probe.auf` (`inst_closed_ex`, verified) |

### Contexts (Typing/Basic.lean:6-8)

| axiom | verdict | justification |
|---|---|---|
| `lookup_z` (154) | T | `Lookup (ty::Γ) 0 ty.lift`, where `lift = liftN 1 · 0` gives `lift 1 0` |
| `lookup_s` (156) | T | `Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift`. The head is the innermost binder, as in Lean4Lean |

### Judgment (IsDefEq, Typing/Basic.lean:18-56)

| axiom | verdict | justification |
|---|---|---|
| `ty` (166, def) | D | `HasType` = diagonal (Basic.lean:60) |
| `sty_nil`, `sty_app` | D | `sty G h A e T`: `e` is `h` applied to `a1 … an`, `A` is a `Π` telescope over them as written (no conversion between the steps), `ai` has the type of the `i`-th binder at `a1 … a(i-1)`, and `T` is the rest. A computing relation (mode `+*++-`: `T` from the rest, the head given up to its constructor, `lean0 modes`). It types a constructor's result (`cwf`) and a nested occurrence (`nst_ty`), which need every argument in the head's domain: a typing of the whole term gives that only by inversion of its derivation (§4, 2026-11-04; the iota, quotient and projection rules, which took it too, are closed equations now) |
| `bvar_ty` (168) | T | :19 |
| `deq_symm` (170) | T | :20 |
| `deq_trans` (172) | T | :21, same type `A` on both premises |
| `sort_df` (174) | T, WF dropped | :22-24. The result type is `sort (succ l)` with the **left** `l`, as in Lean4Lean. Dropping WF is sound (§1) |
| `app_df` (176) | T | :32-35. The result is `B.inst a` with the **left** argument `a`. `inst nz B a R` is `R = inst B a 0` ✓ |
| `lam_df` (179) | T | :36-39. The body context is `A::Γ` with the **left** `A`, and the result is `forallE A B` (left `A`) ✓ |
| `pi_df` (182) | T | :40-43. Body context `A::Γ` (left), result `sort (imax u v)` ✓ |
| `conv` (185) | T | :44 |
| `beta` (187) | T | :45-47. Premises `A::Γ ⊢ e : B` and `Γ ⊢ a : A`. The result is `e.inst a : B.inst a`, both at `k=0` ✓ |
| `eta` (190) | T | :48-50. `e.lift = liftN 1 e 0` is `lift 1 0 e e1` ✓. The binder type `A` of the λ is the one in `forallE A B` ✓ |
| `proof_irrel` (193) | T | :51-53 (`sort .zero` = `srt lz`) |
| (`constDF`, `extra`) | omitted | replaced by MM0 `def` unfolding, the schema for inductive types (§4) and, for an axiom the development itself declares, an axiom of the certificate (§10); not audited here |
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

(`max (imax u v) v ≈ imax u v` *is* derivable, via `limax_imax` and `limax_self`, axioms then; see
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
using `sort_df`/`c_df` at the leaves, or the generator must emit a per-def proved lemma.
Nothing new needs to be trusted, but the work is real. Kernels hit this case when comparing
`f.{max u v}` with `f.{max v u}`.

### 3. (Low, a proof obligation on generated files, not on this file)

The shortcuts are sound for this file's five constructors. Every later `term` of sort `expr`
must keep the model valid:

* `closed nz (c us)` is valid only for constants without `expr` arguments. `.const` is
  `ClosedN`-trivially closed, `lit` is fine, and `proj` is not.
* Any `expr`-argument term (`proj`, §4.5) needs structural `closed_/lift_/inst_` axioms that
  recurse into its arguments. Without them `lift_closed`/`inst_closed` remain sound but useless
  for it, and the lift/inst relations become incomplete. A careless `closed k (proj i e)`
  without a premise on `e` would be **unsound**.

### 4. (Info/doc)

* The header (lines 6-10) says each `term` constant gets a generated `constDF` axiom. It should
  also say that it gets a `closed nz` axiom (as in `consts.mm0`), and that this is valid only
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
* **Argument order.** Every use matches its definition: `inst nz B a R`, `inst nz e a r`,
  `lift 1 0 e e1`, `lift k 0 a a2`, `lift 1 0 A A2`, and `lift_closed`/`inst_closed`
  with `(closed j, j ≤ k) ⇒ op at k`.
* **Annotation side.** Every rule uses the left-hand annotation, exactly as in Lean4Lean.
* **WF drop, `inh_i`, non-functionality, hypothesis-only variables.** All sound (§1).

## 4. Level case splits, the inductive schema and the generated per-declaration axioms

### Level case splits (`spec/lean.mm0`, Part III "Level equivalence")

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

### The inductive schema (`spec/lean-ind.mm0`)

Lean4Lean leaves inductive well-formedness as `sorry` (`VInductDecl.WF`), so this part of the
spec is new trusted design, transcribed from the kernel (`inductive.cpp`; read through its
port `Lean4Lean/Inductive/Add.lean`, cited by function below). The schema has two duties:
*consistency* (every axiom holds in the set-theoretic model of Carneiro's thesis, extended
to interpret the new terms) and *adequacy* (it derives what the kernel accepts; stricter is
sound but incomplete). The generator (`lean0/src/induct.rs`) proves the relations with a
Horn-clause prover over the spec's own axioms (`mm0kit/src/horn.rs`), derives each
recursor's type and each rule's right-hand side, and compares them with the export's before
it states anything; so every block of every certified environment is an adequacy test of
the derivations, but the arguments below must stand on their own.

**Representation.** A block is `ind_mk b P T N`: an atom `b` (a `term X_blk: blk` per block,
so that structurally equal declarations stay distinct), the parameters `P` as a `ctx`
(innermost first, each type under the earlier ones) and the types `T`, each with its type
`F = Π indices, srt l` (under `P`) and its constructors' types. A constructor type is
written under `P` and, outside `P`, under the block's `n` types as variables: at depth `d`
type `j` is `#(d + np + j)`. Binder type annotations (`outParam`, `optParam`, ...) are
consumed, as the kernel does before it builds recursors (`withLocalDecl ...
dom.consumeTypeAnnotations`), so the data states the declaration the kernel works with; the
exported types of the type formers and constructors (annotations kept) are reached by a
definitional cast, which the certificate proves (§8 says what the checker compares).
`ind_ty D i`, `ind_ctor D i c` and `ind_rec D i v` are the block's constants; `proj b i e`
the projections. `N` lists the block's nested occurrences (below); it is `[]` for a block
without any.

**Model.** In outline (the definitions are `model-ind.mm0` and `model-rec.mm0`, the rules
`model-fold.mm0`, `model-nst.mm0` and `model-ci.mm0`; §11): a legal block (`ind_wf`) is
interpreted by families of sets over the parameters and indices, the least fixed point of
its constructors' operator (positivity makes the operator monotone, the universe conditions
keep the fixed point in `srt l`), each element tagged by the constructor and the field
values; `ind_ctor` is the tagging injection and `ind_rec D i v` the fold, which exists for
every motive family in `srt v` whenever `elim_ok` holds. A block that is not legal has a
failure value: it is typed by no rule but `ind_ty_ty`, which needs only `tys_ok`. `proj b i
e` is the `i`th component of an element of a structure-like type. `eeqv e e2` holds only for
terms of the same shape at equivalent levels, which have the same value (`hfin_minv`).

**Functionality.** A relation that computes a term (`rec_ty`, `rec_rhs`, the telescope
relations) is sound only if every derivation yields the right term, so each one's clauses
are exclusive by the shape of its inputs (one clause per constructor of the term walked,
`add` premises for de Bruijn offsets, indices read off the head variable by `spine`; checked
mechanically by `lean0 modes`, *Functionality* below). The exceptions are the disjunctions that the kernel also has (`ulevel`,
`elim_ok`, `large`, `fir`, `proj_ok`, `ipos` whose cases overlap but all hold). The `add`
offsets follow the convention above; the audit of each relation below says which binders
are in scope at each point.

| axioms | argument |
|---|---|
| reading (`ind_data`, `nth_ty`, `nth_ctor`, `clen`, `clen_c`, `ntys`, `minor_idx`, `npis`, `nth_pi`, `isort`, `ind_arity`, `nidx`, `nfields`, `cnth`) and telescopes (`pis`, `lams`, `capp`, `pargs`, `spine`, `rehead`, `has_arg`) | Definitional clauses of functions on syntax; no semantic content. `pargs X d n e` is `X` applied to the `n` variables above depth `d`, outermost first (`#(d+n-1)` first), as a telescope's binders are applied to. |
| `closed_ind_ty`, `closed_ind_ctor`, `closed_ind_rec`, `closed_proj`, `lift_proj`, `inst_proj` | The constants are closed, and `proj` is structural for the three relations, as `.proj` in `VExpr`. |
| `sinst` | Puts the block's types in for the variables above the parameters: `inst k e (ind_ty D j)` instantiates `#k` (type `j` after types `0..j-1` are gone, which moved it down) by a closed term; `inst` lifts by `k`, which leaves a closed term unchanged. |
| `iargs`, `indapp` (`isValidIndApp`) | At depth `d`, `#(d+np+j)` applied to exactly the parameters (`pargs #t d np`: `#(d+np-1) .. #d`) and `nidx D j` indices, each without an occurrence of the block (`closed (d+np)`: every variable at or above `d+np` is a block type). |
| `ipos` (`checkPositivity`), `recfield` (`isRecArg`) | `ipos`: no occurrence, or `Π` over a domain without one (the kernel: an occurrence in a domain is non-positive), or a valid occurrence. `recfield`: a valid occurrence under `Π`s (a reflexive field). Both syntactic where the kernel uses `whnf` first; a block where that matters is an error of `lean0 gen`. |
| `ulevel` (`checkConstructors`' universe test) | `l ≈ 0` or `l ⊔ u ≈ l` are the semantic readings of `isAlwaysZero` and `geq'`, which are sound approximations of them: whatever the kernel accepts, these accept, and both conditions are what the fixed point in `srt l` needs (a type in `Prop` may have fields of any size; otherwise each field's universe is at most the type's). |
| `cwf`, `ctors_wf` | Each field's type (with the block's types put in) is a type in the context of the parameters and the earlier fields (`⟦ₜ Ctx ⊢ A2 : srt u ⟧`), of an allowed level, positive; a recursive field is not mentioned in the rest of the constructor type (`cwf_pi_rec`: the rest is a lift, `lift 1 0 B2 B`; a non-recursive field, `cwf_pi`, has no occurrence of the block, `closed k A`); the result is the constructor's own type applied to the parameters and to indices without occurrences, each argument of the result (with the block's types put in, `K2`) typed at its binder's type in the type former's type `Π P, F_i` (`sty Ctx (ind_ty D i) R2 K2 S`, `R2` that type lifted over the fields and parameters, as in the iota rules). The kernel types the indices by `checkType` of the whole constructor type; the spec states each argument's typing, since in the model a typing of the result as a whole says nothing about its arguments (an application outside a function's domain denotes `∅`), and the indices' typing is what puts a constructor's value in the family at an index of the family's domain (until 2026-11-11 the clause had only `indapp`, which accepted an index of the wrong type: `IX.mk : IX E` for `IX : Prop → Type`). This is `checkConstructors`, with the parameters matched syntactically (the data has one telescope `P`) where the kernel uses `isDefEq`; the generator checks that before it states the data, else the block is an error. The non-occurrence of recursive fields (added 2026-11-12) is implied by the kernel's typing (a term that mentions a field of type `T` mentions `T`, which neither a positive field's domain nor an index may do; the kernel also rejects a nested occurrence whose arguments mention a field), so it rejects no block the kernel accepts; it is stated because the model sees only that the typings hold, not that they are derivable, and without it a field's domain could grow with a recursive field's value and the family leave the universe. Each constructor type is closed over the parameters and the types (`ctors_wf_cons`: `Π P, K` is `closed n`, added 2026-11-12), for the reason `tys_closed` gives: `ind_ctor D i c` is a closed constant. |
| `tys_ty`, `tys_ok`, `ctx_wf`, `tys_wf`, `ind_wf`, `tys_closed` | `checkInductiveTypes`: the parameters and the types' types are closed (`tys_closed`: `Π P, F_i` is closed for each type; the kernel's blocks are closed constants, and the model's values of a block's constants are the same at every valuation of the context, so a block whose parameters mention the context could not have the types `ind_ctor_ty` gives it in every context; added 2026-11-12), the parameters are types over the earlier ones, each type's type is a type of the form `Π indices, srt l2` with `l2 ≈ l`, the block's universe being the first type's (the kernel: `isEquiv`). `tys_ty` also requires each type's type to be binders over a sort (`isort`; added 2026-11-15): `ind_ty_ty` has only `tys_ok` as its premise, and without this a block whose type's type is a typed non-sort such as `False` would make `ind_ty D 0` a proof of it (lean0's generator refuses such a block before the schema sees it, so no negative test shows the premise at work). `tys_ok` alone types the type formers (the kernel adds them before it checks the constructors; in the model an illegal block's types are empty families, so typing the formers needs no legality). |
| `elim_ok`, `large`, `fir`, `leaf_has` (`isLargeEliminator`) | `v ≈ 0` always (small elimination). Large elimination when `ls lz ⊔ l ≈ l` (never a proposition, `isNeverZero`), or one type with no constructors (empty: the fold is vacuous), or one type with one constructor each of whose fields is a proposition (`⟦ₜ Ctx ⊢ A2 : srt lz ⟧`, where the kernel tests `isAlwaysZero` syntactically) or occurs as an argument of the constructor's result (`has_arg`, a syntactic occurrence as a whole argument, as the kernel's `contains`): subsingleton elimination, since such a type has at most one element per index under proof irrelevance, so the fold into any universe is determined. |
| `mty`, `motives` (`mkRecInfos`' motives) | Motive `j` is `Π indices, Π (ind_ty D j params indices), srt v`, read off `F_j` lifted over the `j` earlier motives: at depth `d` inside it the parameters are `#(d+j+np-1) .. #(d+j)` and the indices `#(d-1) .. #0`. The context lists motive `n-1` first (innermost): `capp Mr (Mj :: [])` appends the outer one. |
| `ihty`, `mwalk`, `cminors`, `minors` (minor premises) | Minor `k` for constructor `c` of type `i` is `Π fields, Π ihs, motive_i indices (ind_ctor D i c params fields)`. `mwalk` walks the constructor type at depth `d` with `r` recursive fields passed: a field type is lifted by `k + n` at depth `d` (over the `k` earlier minors and `n` motives, which sit between the parameters and the fields); a recursive field's hypothesis is its type lifted by `r + nf - d` (over the hypotheses before it and the fields after it), with the head `ind_ty D j params` replaced by motive `j` at `#(y + r + nf + k + n - 1 - j)` under `y` binders of its own telescope, applied to the field `#(y + r + nf - 1 - d)` and those binders. The hypotheses are collected innermost first (`IH :: Ihs`). At the leaf (`d = nf`, which `mwalk_res` requires by using one variable for both) the result is lifted by `k + n` at depth `nf` and by `r` at depth 0, its head `#h` (the type variable, so lifted) applied to `np` arguments is replaced by motive `i` at `#(r + nf + k + n - 1 - i)`, and the constructor is applied to the parameters `#(r+nf+k+n+np-1) ..` and the fields `#(r+nf-1) .. #r`. `cminors`/`minors` append each next minor outside the later ones. The type index `j` of a recursive field is an argument of `ihty` (`ihty D np n mo fld y j A IH`), passed by `mwalk_pi_rec` from `recfield`, which reads it off the field's type before the block's types are put in; `ihty_app` requires the lifted type's head to be `ind_ty D j` for that same `j`, so the relation holds for no more hypotheses than when it read `j` off the head itself, and the model's fold and the minor's type name the same motive by construction. |
| `rtail`, `rec_ty` | `Π P, Π M, Π N, Π indices, Π major, motive_i indices major`, with `F_i` lifted over the `m + n` motives and minors; under the indices (depth `d`) and the major, motive `i` is `#(d + m + n - i)` and the indices `#d .. #1`. This is the kernel's `ty` in `AddInductive.run`. |
| `ihval`, `rwalk`, `rec_rhs` (`mkRecRules`) | `λ P, λ M, λ N, λ fields, minor_k fields ihs`, the minor at `#(nf + m - 1 - k)` under the fields; each recursive field's hypothesis is `λ ys, ind_rec D j v params motives minors indices (field ys)`, with the recursor's arguments the variables above the fields: parameters at `#(y+nf+m+n+np-1) ..`, motives and minors `#(y+nf+m+n-1) .. #(y+nf)`, the field at `#(y + nf - 1 - d)`. As in `ihty`, the type index `j` is an argument of `ihval` (`ihval D np n m v nf fld y j A IH`), passed by `rwalk_pi_rec` from `recfield`. |
| `ind_ty_ty`, `ind_ctor_ty` | The type former has type `Π P, F_i` under `tys_ok`; constructor `c` of type `i` has type `Π P, K` with the block's types put in (`ctor_ty`, a relation of Part I since 2026-11-17, so that the iota and projection rules can name the type), under `ind_wf`: in the model, the families and the tagging injections have these types. |
| `ind_rec_ty` | Under `ind_wf` and `elim_ok`, the fold has the type `rec_ty` computes (the thesis's recursor; the argument that `rec_ty` computes the kernel's type is the two rows above, tested on every block). |
| `clift`, `psplit`, `iota_tel`, `iota_lhs`, `iota_eq`, `crst`, `ind_iota_eq` | Iota as a closed equation: `ind_wf Dl D`, `elim_ok Dl D v`, `iota_eq D i c v Dl0 lhs0 rhs0 T0`, `ind_nested D N`, `crst D N Dl0 Dl` and `rst D N` of `lhs0`, `rhs0`, `T0` to `lhs`, `rhs`, `T` give `Dl ⊢ lhs ≡ rhs : T`: `iota_eq` states the equation over the block's own types and constructors, and the rule restores the auxiliary ones to the nested occurrences in the context (`crst`: `rst` entry by entry), the two sides and the type (nothing changes when `N` is empty: `rst_nil`). The unrestored context, sides and type are variables of the rule, not of a relation, so that they have sorts in the reduction. `iota_eq` (Part I, one clause) puts together the context `Dl` of the recursor's own variables (`iota_tel`: the parameters `P`, the motives, the minors, then the constructor's fields `X`, which `clift` moves under the motives and the minors; `psplit` splits the constructor's type with the block's types put in, `sinst`, at its `npis` binders into `X` and the result `res`), `ind_rec D i v ps ms ns is (ind_ctor D i c ps fs) ≡ Rh ps ms ns fs` at the type `motive_i is (ind_ctor D i c ps fs)` (`iota_lhs`: `ps`, `ms`, `ns`, `fs` are the context's variables, by windows `pargs`; the indices `is` are those of the constructor's result `res`, lifted under the motives and the minors and read off by `rehead`; `Rh` is `rec_rhs`'s term). The rule has no typing premise, since every argument is a variable of the context at its declared type or an index of the constructor's own result (typed by `cwf_res` in `ind_wf`): so the constructor's parameters are the recursor's and its indices the recursor's by construction, where a rule over arbitrary arguments would need typing premises to say so (the previous row's example); it is Lean4Lean's form of a recursor rule (a closed equation over shared variables). An instance at terms in a context `Γ` follows by `weak_base_df` (§6: the equation over `Γ` as base context) and `inst_df` once per variable, from the parameters on, whose premises are the typings of the terms substituted; the generator proves the equation once per recursor rule (`X_rec_c_iota`, with the closedness of the rule's definition, `X_rec_c_closed`) and uses it at every iota step (`Elab::iota_closed`: the instance has the constructor's own indices and, in the major premise, the parameters and levels of the major premise's type in the recursor's type, which are the recursor's own or, for the recursor of an auxiliary type, the nested occurrence's arguments at the recursor's parameters; the term at hand is equal to the instance by congruence). At an auxiliary type `i` the restored equation is the recursor `X.rec_k` (`mkAuxRecNameMap`) on the constructor of the occurrence's block, `ind_rec D i v ps ms ns is (ind_ctor I ii c Ds[ps] fs) ≡ R ps ms ns fs`, the fields being the last arguments of the major premise as in `inductive_reduce_rec`. All of Init (census of 2026-11-21): 3.3 million iota steps, each by this rule. The relations have computing premises only. In the reduction the rule is a theorem at every block (`spec/tg/model/model-ci.mm0`, audit §11): at a valuation of the unrestored context the arguments lie in their spaces because the valuation does; the restored context has the same valuations, and the restored sides and type the same values, because every auxiliary type and constructor in them sits on the parameters' variables (the specialization lemma of nested blocks, `spec/tg/model/model-nst.mm0`: `iota_tel_rst_sat`, `iota_lhs_rst_val`, `rec_rhs_rst_val`). `rst` is not a function (`rst_refl`): the rule holds for every result. |
| `struct_like`, `field_ty`, `proj_ok`, `fprops`, `pinst`, `qinst`, `proj_ty` | Typing of `proj b i e` for `e : ind_ty D j ps`, type `j` structure-like (one constructor, no indices; the kernel's `is_structure_like`, which a type of a mutual block may satisfy): the field's type with the parameters and then the earlier projections put in, outermost first (`pinst` recurses to the innermost argument of `S` and substitutes on the way out; `qinst` fields `0 ..` at `#(k-1) ..`), a simultaneous substitution since each term substituted is lifted over the binders below it. `proj_ok`: the type's sort is at least 1, or the fields up to `i` are propositions (`fprops`: each `⟦ₜ Ctx ⊢ A2 : srt lz ⟧`) — the argument of stage A's `_dfp`: such projections are definable by elimination into `Prop`, and nanoda requires less (only the dependent fields), so this is no more permissive. |
| `proj_eq`, `proj_mk` | The projection of a constructor application as a closed equation, in `ind_iota_eq`'s shape: `ind_wf Dl D`, `proj_ok Dl D j i`, `proj_eq D j i Dl0 lhs0 k`, `ind_nested D N`, `crst D N Dl0 Dl`, `rst D N lhs0 lhs` and `lookup Dl k T` give `Dl ⊢ lhs ≡ #k : T`. `proj_eq` (Part I, one clause) puts together the context `Dl0` of the parameters `P` and then the first constructor's fields `X` (`psplit` of its type with the block's types put in, `sinst`, at its `npis` binders; `capp X P`), the left-hand side `proj b i (ind_ctor D j 0 @ ps @ fs)` with the block's own atom `b` and `ps`, `fs` the context's variables (windows `pargs`), and the index `k = nf - 1 - i` of field `i`'s variable; the rule restores the auxiliary types to the nested occurrences in the context and the left-hand side (nothing changes when `N` is empty) and reads the field's type off the restored context (`lookup`). The field may be projected (`proj_ok`, as in `proj_ty`: for a structure that is a proposition the value has no fields, so the fields up to `i` must be proofs). No typing premise: every argument is a variable of the context, so it lies in the constructor's domain by the context itself (until 2026-11-22 the rule was schematic in the arguments, with a typing of the constructor's spine along its type, `ctor_ty` and `sty`, and of the projection; a typing of the projection alone says nothing about the arguments, whose application has the value `∅` in the model outside the constructor's domain). Instances follow by `weak_base_df` and `inst_df`: the generator proves the equation once per field (`S_proj_i_mk`, over any base context, with `proj_ok`'s level premises) and each use types the parameters and the fields at their binders. In the model: a valuation of the restored context is one of the unrestored (`proj_tel_rst_sat`), the restored left-hand side keeps its value (`proj_lhs_rst_val`), and there the constructor's value at the valuation is its point at a path of its type, whose field `i` is the valuation's entry (`proj_ci_wf`, `proj_mk_eq_rule`). |
| `nonrec`, `eta_ok`, `projs`, `eta_eq`, `ind_eta` | Eta for a structure-like type none of whose fields mentions the block (`closed (d + np)` for each domain): `e ≡ ind_ctor D j nz ps (proj b 0 e) ... (proj b (nf-1) e)` at `e`'s type, since such a type is a product in the model. The rule is a closed equation in the shape of `ind_iota_eq` and `proj_mk`: `ind_wf Dl D`, `eta_ok D j` and `eta_eq D j Dl M S` give `⟦ Dl ⊢ #0 ≡ M : S ⟧`, where Part I's `eta_eq` (one clause) builds the context `Dl` of the parameters and one variable of the type applied to them (`pargs`), that type as the variable has it (`lift`), and `M`, the constructor applied to the parameters (`rehead`) and to the projections of `#0` (`projs`). No typing premise and no restoration (the type is a declared one, and its parameters mention no type of the block). Instances follow by `weak_base_df` and `inst_df`: the generator's `S_eta` is the equation over any base context, and each use types the parameters at their binders and the term at the structure type. Until 2026-11-22 the rule was schematic in `e`, with its typing as a premise; the model proves the closed equation from that one at the variable (`ind_eta_eq_rule`). (The kernel requires the block not to be recursive at all; this accepts a non-recursive type of a recursive mutual block too, which is still a product.) |
| `ind_nested`, `ndecl`, `cnth`, `aux_of`, `rst`, `spz`, `nst_hit`, `afree`, `spz_ctors`, `aux_data`, `nst_ok`, `nst_ty`, `nst_group`, `pinst_head_c` (nested blocks, B2; `ElimNestedInductive`) | A nested block `ind_mk b P T N` (`N` not empty) is the mutual block the kernel checks in its place: `T` lists the declared types and then one auxiliary type per nested occurrence `I Ds` of an earlier block `I` (in the kernel's order), and `N` the occurrences, each `ind_ty I i @ Ds` written like a constructor type at depth 0 (`Ds` mention the block's types; the kernel requires them to mention no bound variable, and a parameter `Ds` that mentions none makes no occurrence, so the certificate's `N` must be the kernel's list, which the checker's comparison of the recursor types enforces, §8). Every relation of the schema (`ind_wf`, `elim_ok`, `rec_ty`, `rec_rhs`, `struct_like`, `eta_ok`, ...) reads the mutual data, as the kernel runs `AddInductive` on the specialized block; two additions make it the kernel's nested block. (1) `nst_ok` (a premise of `ind_wf`): the occurrences come in groups, one per declared type of a well-formed block `I` in order with the same arguments (`I.all`, which excludes `I`'s own auxiliary types; `I` declares at least one type, `0 < ni0`), a group's arguments are typed at `I`'s parameters in the block's parameter context with the block's types put in (`nst_ty`: `sty` at the type of `I`'s first type, as `cwf_res` types a constructor's result: the specialized constructors mention only the auxiliary type, so without this premise nothing would say that `I Ds` is a type, and `ind_ctor_ty`, which restores it, would state a type with no meaning; the arguments are also closed over the block's parameters, `closed np X1`, as the kernel's are: without it they could mention the context `G`, and the closed constant `ind_ctor D i c` would have a restored type that changes under `inst_df`), and each auxiliary type's data is `I`'s type's type at `Ds` (`pinst`) and `I`'s constructors specialized (`spz_ctors`: `I`'s types put in by `sinst`, `I`'s own occurrences restored by `rst` since `I` may be nested, the parameters replaced by `Ds` by `pinst`, then `spz`, which replaces each occurrence `I' Ds' is` of `N` at depth `d` by `#(d + np + j)` applied to the block's parameters and to `is`, from the outside in as `replaceAllNested` does; the lookup `nst_hit` tries the entries by clause alternatives, since the prover does not re-enter a finished premise). So the auxiliary types are exactly the kernel's `_nested.X_k`, and `tys_wf` on the mutual data is the kernel's positivity and universe check on them. (2) `rst D N e e2` (`restoreNested`): `ind_ty D j ps is` for an auxiliary type `j` is read as `I Ds[ps] is` (`sinst` then `pinst`, the parameters applied being the ones substituted) and `ind_ctor D j c ps fs` as `ind_ctor I i c Ds[ps] fs`; nothing else changes, and the identity when `N = []` (`rst_nil`; `rst_refl` is the last clause so that an unknown result is computed by the traversal). `ind_ctor_ty`, `ind_rec_ty`, `proj_ty` (the field's type, before the parameters and projections are put in, so that the substitution hypotheses of the structure lemmas match) and iota (`ind_iota_eq` restores its context, both sides and the type; the unrestored ones are variables of the rule) restore what they state. *Model.* The auxiliary type `j` of a legal nested block is interpreted as the family `I Ds` itself: by (1) its constructors are `I`'s at `Ds` with the occurrences written as the block's own types, so the mutual fixed point's component `j` and the family `I Ds` (the fixed point of `I`'s operator at the parameters `Ds`, which the mutual fixed point already contains) satisfy the same equations, and the least fixed point is unique; this is the kernel's justification for restoring. Under that reading `rst` is the identity on values, so the restored typings are the mutual block's, and the restored iota equation is the mutual block's for the constructor `ind_ctor D i c`, whose value is `ind_ctor I ii c Ds[ps]`'s. `rst` is a search relation (`rst_refl` may leave any subterm as it is), so `spz_ctors_cons` also requires `afree K2` of the restored constructor: no `ind_ty D j` or `ind_ctor D j c` in it has `j` among `D`'s auxiliary types. That holds of every term Lean exports, which mentions no auxiliary type (the generator restores from the outside in and proves the premise as the other checking relations; no generator change, and no negative test: the restored constructor is computed by the generator, not read from the export). A premise can only make the relation less permissive; with it the restored constructor is unique, which the model's proof for a nested block that is nested itself uses (two blocks specializing the same inner constructor get the same one). `ind_eqv` compares `N` as well as `P` and `T`, since two blocks with the same atom and mutual data but different occurrences denote different families. The elimination level and `is_rec` (no eta for a structure with a nested field) are the mutual block's, as in the kernel. |
| `eeqv_*`, `ind_eqv`, `ceqv`, `teqv`, `cseqv`, `lseqv`, `eeqv_df` | `eeqv` is the structural congruence with `leqv` at sorts and recursor levels, `ind_eqv` (same atom, componentwise `eeqv`) at the block constants, and `lseqv` (entrywise `leqv`) at an opaque constant's levels (`eeqv_cst`: the same atom; the atom's interpretation is a function of the levels' values). `eeqv_df`: expressions of the same shape at equivalent levels denote the same value, so they are defeq at any type of one of them (this generalizes `sort_df` and `constDF`). A generated term that is not a public definition (an opaque, an axiom, a theorem, a stage-A constant) has no `eeqv` clause, so a block whose data mentions one at its levels gets `axiom c_eeqv (us us2): leqv u u2 > ... > eeqv (c us) (c us2)`, once per constant (`induct::eeqv_axioms`; the generator's report counts them): the same constant at equivalent levels, which is what `eeqv` means. `lean0 check` checks its shape (§8). A `_df` lemma whose `eeqv` still fails is stated as an axiom and counted. |
| `nat_D`, `eq_D`; `quot_atom`, `quot_mk_atom`, `quot_lift_atom`, `quot_ind_atom` and the defs `quot`, `quot_mk`, `quot_lift`, `quot_ind`; `quot_ty`, `quot_mk_ty`, `quot_lift_ty`, `quot_ind_ty`, `quot_lift_mk` | Lean's prelude blocks `Nat` and `Eq` are stated as spec data (between the spec's `lean0-check` marks, in prefix form), so that the quotient primitives' types (which mention `Eq`) and the literal ties (§5) can be spec axioms. The generator uses them only when the export's block is exactly this data (else the block is generated as usual, and the quotient primitives are an error: no axioms are generated for them); `lean0 check` compares the export's `Nat` and `Eq` with them like any block (§8). The quotient primitives are constants with the types the kernel requires when it adds them (`quot.cpp`, `check_quot_decls`: `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` have exactly these types, with `Eq` checked to be the expected inductive), and they are constants like any other: `cst` of an atom of the spec at the list of their levels (since 2026-11-23; four expression constructors with their own clauses of `closed`, `afree` and `eeqv` before), so closedness and level invariance are `closed_cst` and `eeqv_cst`. The reduction rule is `Quot.lift f h (Quot.mk r a) ≡ f a` (Lean4Lean's quotient `extra` rule), stated once as a closed equation in the context of the primitive's own variables (`α`, `r`, `β`, `f`, `h`, `a`, at the type `β`), with no premise: every argument is a variable of the context, so `Quot.mk`'s `α` and `r` are the primitive's and `a` is in `f`'s domain by the context itself. Instances follow by `weak_base_df` and `inst_df` (the generator's `Quot_lift_mk` is the equation over any base context, and each use types the arguments at their binders, where nanoda's `reduce_quot` checks only the spine). Until 2026-11-22 the rule was schematic in the arguments, with a typing of the spine (`sty`) and of `a` at `α` (when `α` is a proposition the typing of `Quot.mk r a` as a whole says nothing about `a`); the model proves the closed equation from that. The kernel's other reduction, `Quot.ind h (Quot.mk r a) ≡ h a`, has no rule: both sides are proofs of `β (Quot.mk r a)`, so the generator certifies the step by `proof_irrel` (test `quot_ind_ex`). Sound in the model: the quotient of a type by a relation, with `Quot.lift` well defined by its hypothesis and `Quot.ind` by induction on representatives. |

**What `ind_wf` does not say.** Duplicate constructor names, `checkNoMVarNoFVar`, the
`_nested` prefix: naming matters, not typing. The syntactic places where the kernel uses
`whnf` (`isRecArg`, `checkPositivity`, the parameter match) make a block an error of `lean0
gen`: no axioms are generated for an inductive type (until 2026-11-22 such a block got
generated axioms, "stage A"; Init has no such block), and `lean0 check` requires every
inductive type, constructor and recursor of the export to be a member of a block's data.

**Negative tests.** The relations that compute a term (`rec_ty`, `rec_rhs`, the projections'
types) are checked against the kernel on every block, as said above, but the relations that
check a block (`ipos`, `ulevel`, `tys_wf`, `elim_ok`, ...) can only be too permissive, which
no legal export shows. Lean's kernel elaborates no illegal block, so `scripts/illegal-export.py`
makes one by one change to the export of `tests/lean/Illegal.lean` (legal blocks of the same
shapes, all certified by the schema), and `scripts/test.sh` runs `lean0 gen --unchecked` on it,
which skips nanoda's check so that the schema alone judges the block; the run must fail at the
block, naming the schema. The cases, and the relation that rejects each: a non-positive
occurrence `(NP → NP) → NP` (`ipos`: the domain is neither free of the block nor a valid
occurrence); a field `Type` of a type in `Type` (`ulevel`); a recursor of a proposition with two
constructors into `Sort u` (`elim_ok`); a mutual block with one type in `Type` and one in
`Type 1` (`tys_wf`); a constructor whose result is `W (W α)` (`cwf_res`, through `iargs`); a
field `V (V α)` (`ipos`, through `indapp` and `iargs`); a constructor `IX E` of `IX : Prop →
Type`, the index of the wrong type (`cwf_res`, through `sty`). nanoda rejects all seven as well
(two by not terminating, `historical/upstream-issues.md`). An eighth case is nested: the
occurrence `Ph NO E` of `Ph (α β : Type)` becomes `Ph NO Type` (`nst_ty`, through `sty`).

**Functionality (`lean0 modes`, `mm0kit/src/modes.rs`).** The reading of a relation as a
function, or a predicate, is checked mechanically. Every relation of the spec other than the
rule heads `deq`, `leqv` and `inh` has a declared kind and mode (which arguments are inputs),
and the check establishes that each clause is well-moded (the inputs of every computing
premise, and the clause's outputs, are determined by the clause's inputs through the premises,
so the clause is a defining equation with the checking premises as side conditions) and that
the clauses of each computing relation are pairwise exclusive on the inputs: their heads do
not unify on the input positions; or their arithmetic premises contradict each other (`i < k`
against `k ≤ i`, decided as difference constraints); or a premise then has no clause that can
apply, to a small depth (`recfield` on a `Π` type, `spine` with a constant head on a `Π`); or
the two clauses agree on the overlap (`badd_0l`/`badd_0r` at `0 + 0`). Two overlaps are
declared with their reason, and the check requires the declared list to be exact:
`lift_closed`/`inst_closed` (admissible clauses computing the same value) and
`mwalk_pi_nr`/`mwalk_pi_rec`, `rwalk_pi_nr`/`rwalk_pi_rec` (a recursive field is not closed
above the parameters). The relations that are not functions are declared as such: the
checking relations (`ipos`, `cwf`, `elim_ok`, ..., where the kernel's disjunctions are), and
`rst`, whose clauses are tried in order (`rst_refl` last) and which admits every partial
restoration, sound since an auxiliary type denotes its occurrence (below). Totals (2026-11-26): 120
relations with 173 computing clauses, 115 checking clauses and the 8 clauses of `rst`, and 71
rules. `scripts/test.sh` runs the check and requires a spec with an overlapping clause to be
rejected.

### Lean's axioms `propext` and `Quot.sound` (`spec/lean-quot.mm0`)

`propext_ty` and `quot_sound_ty` give the two constants the types Lean's library declares for
them (`propext : Π (a b : Prop), (a ↔ b) → a = b`, with `Iff` as the spec's block `iff_D`, compared
with the export's like `Nat` and `Eq`; `Quot.sound : Π α r a b, r a b → Quot.mk r a = Quot.mk r b`).
The constants are `cst` of two atoms that the spec declares (`propext_atom`, `quot_sound_atom`), so
closedness and level congruence are `closed_cst` and `eeqv_cst`, and no syntax is added. Sound
because both types are true propositions in the model, whose proofs are all `∅`: for `propext`,
propositions are the truth values `∅` and `{∅}`, the two fields of an `Iff a b` are functions both
ways between them (`proj_ty` at `iff_D`), so they are equal sets (`two_iff_eq`), and the model's
`Eq` is equality (`meqs_i`); for `Quot.sound`, the quotient is the set of classes of the
equivalence the relation generates, so related elements have the same class (`qmk_rel_eq`).
Machine-checked: model-quot's `propext_inh` and `quot_sound_inh`, and the two rules in model-ci
(§11). The model's environment of opaque constants is cut at the two atoms (`Envx`), where the
value is `∅`.

### Lean's axiom `Classical.choice` (`spec/lean-quot.mm0`, `spec/tg/tg.mm0`)

`choice_ty` gives `choice u`, a `cst` of the spec's atom `choice_atom`, the type
`Π (α : Sort u), Nonempty α → α`, with `Nonempty` as the spec's block `nonempty_D` (compared with
the export's). Unlike the other two axioms its type is not a proposition, so the constant needs a
value that is a term: a function choosing an element of every inhabited type of a universe. The
axiom of choice in the form "every set has a choice function" proves such functions to exist but
names none, so the base file states choice through an operator instead (2026-11-22, the user's
decision): `term ch (a: set): class` with `ax_choice`, `∃ x (x ∊ a) → ch a ∈ a`, and the
operator's substitution equation `sb_c_ch`. The former axiom (`∃ f chooses f a`) is the theorem
`choice_ex` of `hartogs.mm0` (the operator's graph on `a`), so the library is unchanged above it.

*What the operator costs.* The base is Tarski–Grothendieck set theory with a global choice
operator in place of the axiom of choice, and its schemas (replacement, in the form of
`ax_replace` over any class term) apply to terms that mention `ch`. This is a conservative
extension: a statement that does not mention `ch` is provable with the operator only if it is
provable from the axiom of choice. For ZFC that is Felgner's theorem (U. Felgner, "Comparison of
the axioms of local and universal choice", Fund. Math. 71, 1971: a global choice function can be
added to a countable model by forcing with set-sized partial choice functions, which adds no
sets and keeps the schemas in the extended language). It carries over to TG by the deduction
theorem: Tarski's axiom is one sentence `T` without `ch`, so a proof of `P` from TG with the
operator is a proof of `T → P` from ZFC with the operator, hence from ZFC, hence `P` from TG.
Two details of the base's form: `ch a` is a class term, so in first-order terms the new symbol is
a binary predicate `y ∊ ch a`, which Felgner's function `F` interprets as `y ∈ F(a)` (taking
`F(∅) = ∅`), carrying each instance of a schema to an instance for `F`; and foundation is the
schema of `∈`-induction, whose instances with `ch` follow from the axiom of foundation and
separation in the extended language. (The class terms of `tg.mm0` are a notation over
first-order set theory; we have not formalized this argument, and the reference is cited from
memory.) A certified judgment does mention `ch`, through the value of `choice`, so the
statement to trust is the one with the operator; the conservativity says that the operator adds
no risk of inconsistency to TG.

*The model.* The value of `choice` at a level of value `n` is `chv n`, the function taking a
type `a` of the universe `uni n` and a proof that `a` has an element to `ch a` (model-quot;
`chv_cpi`: it is an element of the product over those). The value of `Nonempty` at a type `a` is
the truth value of "`a` has an element" (`tne a`), proved as the model's `Eq` is shown to be
equality: from the rules of `nonempty_D`'s type, constructor and recursor in the model, the
recursor at the motive with that truth value. So `chv n` is an element of the value of the
axiom's type (`choice_mem`). The environment `Envx` has the graph of `chv` at the atom
(`envx_choice`), and the rule is model-ci's `choice_ty`.

### Generated per-declaration axioms (`lean0/src/gen.rs`)

These live in the generated `.mm0`, not in `lean.mm0`, and must be read against the Lean
declaration. They remain only for axioms other than Lean's three standard ones (those the
development declares, and `sorryAx`): the typing of each is assumed. `propext`, `Quot.sound` and
`Classical.choice` are not among them when the export gives them the types of the spec's rules
`propext_ty`, `quot_sound_ty` and `choice_ty` (above): their `_df` statements are then theorems. Nothing else is assumed. No
inductive type, constructor, recursor or quotient primitive has an axiom (a block the schema does
not certify, or a quotient primitive whose type is not the spec's, is an error); no literal
operation has one (equations that are not derived are an error, §5); and an opaque constant is
certified like a theorem, as an abstract definition by its value, which the kernel never unfolds
(`def c (us): expr;` and `theorem c_ty`; until 2026-11-22 it was an atom with an assumed typing,
its value's typing proved beside it).

| axiom class | Lean4Lean counterpart / argument |
|---|---|
| `c_df` (Lean axioms) | `constDF` for a constant whose type is the given `T` (`T` is checked well-typed by the public theorem `c_wf`) |
| `c_atom` (term of sort `atom`) and `c` (def, `cst c_atom (lcons u1 ... lnil)`) | the constant itself: an atom of its own at its levels (§10). `c_closed` is a theorem (`closed_cst`) and the level congruence is the spec's `eeqv_cst`, so neither is an axiom (until 2026-11-04 both were generated axioms, 260 and 24 of them in Init) |
| (`c_eeqv`: `leqv u u2 > ... > eeqv (c us) (c us2)`, for a theorem or opaque constant that an inductive declaration mentions at its levels; above) | not an axiom since 2026-11-22: a theorem, proved where the constant is declared by unfolding it (the proof term at equivalent levels is the same expression up to levels; `induct::theorem_eeqv`, for the constants `gen::eeqv_needed` finds in the export, a set closed under mention in proof terms) |

K-like reduction (`Eq.rec` on a non-constructor) has no axiom: the major premise is replaced by
the constructor using `proof_irrel`.

## 5. Nat literals

### Binary numerals and arithmetic (`spec/lean.mm0`, "Nat literals: binary numerals")

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
because constants have no loose bound variables. The ties to `Nat` are the spec axioms
`lit_zero` and `lit_succ` over the spec's block `nat_D` (§4); in an environment whose `Nat` is
not that block (the generator then declares the block itself) no literal can be certified,
and `lit` is inert.

### Literal axioms: the ties (`spec/lean.mm0`) and the generated operations (`lean0/src/natlit.rs`)

| axiom | argument |
|---|---|
| `lit_zero`: `deq G (lit b0) (ind_ctor nat_D nz nz) (ind_ty nat_D nz)` | in the model, `Nat.zero ≡ Nat.zero : Nat` (`constDF`); `nat_D` is Lean's `Nat`, with `Nat.zero : Nat` by its data |
| `lit_succ`: `bsucc a b > deq G (lit b) (app (ind_ctor nat_D 0 1) (lit a)) (ind_ty nat_D 0)` | both sides denote the same term `succ^(a+1) zero`, which has type `Nat` because `Nat.succ : Nat → Nat` by the data |
| the operations' theorems on literals, proved from the rules below (generated axioms until 2026-11-22, when the equations could not be derived; that is now an error): `Nat_add_lit`, `Nat_sub_lit`/`_lit0`, `Nat_mul_lit`, `Nat_beq_lit`/`_lit_lt`/`_lit_gt`, `Nat_ble_lit`/`_lit_gt`, `Nat_pow_lit`, `Nat_shiftLeft_lit`, `Nat_shiftRight_lit`, `Nat_div_lit`/`_lit0`, `Nat_mod_lit`/`_lit0`, `Nat_gcd_lit`/`_lit2`, `Nat_land_lit`, `Nat_lor_lit`, `Nat_xor_lit` | `op (succ^a zero) (succ^b zero) ≡ succ^(f a b) zero : Nat` (or `≡ Bool.true/false : Bool`), where the premises force the value: `sub` from `c+b = a` or `a+c = b`; `div`/`mod` from `q·b = m`, `m+r = a`, `r+x+1 = b` (so `r < b`, Euclidean division, and `b = 0` has its own axiom: `a/0 = 0`, `a%0 = a`); `gcd` from `g·p = a`, `g·q = b` (`g` divides both) and `x·a = y·b + g` or `y·b = x·a + g` (every common divisor divides `g`, so `g = gcd a b`; `a = b = 0` forces `g = 0`); `beq` false from `a+c+1 = b` or `b+c+1 = a`; `ble` from `a+c = b` / `b+c+1 = a`; shifts via `2^b`. |

**What the operations' rules establish (the trust gap of the former generated axioms).** The statements are valid only if the
environment's definition of the operation computes it on numerals, which is Lean4Lean's
`HasPrimitives` invariant. Lean4Lean establishes it by checking defining equations when the
definition is added (`Primitive.lean`: e.g. `Nat.add x 0 ≡ x` and
`Nat.add x (succ y) ≡ succ (Nat.add x y)` for fresh `x y`; well-founded unfolding through
`WellFounded.Nat.fix`, `dite` and `Decidable` reflection for `gcd`, `div`, `mod` and the
bitwise operations). A generated axiom, like nanoda and the C++ kernel, only checks the name
and the type (`Nat → Nat → Nat`, or `→ Bool` for `beq`/`ble`). Every operation has rules in
the spec (stage B, below), and a certificate has no such axiom: when the derivation of an
operation's equations fails, `lean0 gen` fails. (A sliced export needs nothing beyond the
operation: the structural operations' equations come from their own definitions, and lean0
carries the proofs the division-like ones ask for, below.)

### The literal operations as rules over defining equations (`spec/lean.mm0`, "The defining equations of the literal operations" and Part III "Literals"; stage B)

The spec states, per operation, a relation `*_eqs G f ...` that holds exactly when its
single rule `*_eqs_i` applies: `f` is closed, `f` has the operation's type, and the defining
equations Lean4Lean checks of the environment's definition (`Primitive.lean`, `checkNatAdd`
and so on) hold as `deq` judgments over fresh variables (`#0`, `#1` of type
`nat_ty = ind_ty nat_D nz`, in contexts `nat_ty :: G` and `nat_ty :: nat_ty :: G`). The
rules `nat_*_lit` then give the operation's value on literals. A certificate derives the
equations of the environment's `Nat.add` (etc.) when it is declared, as ordinary derivations
(delta, iota, beta), and states `Nat_add_eqs: add_eqs G Nat_add`; its `Nat_add_lit` (the same
statement as the stage-A axiom) is then a theorem, from `nat_add_lit`. So the kernel's claim
"`Nat.add` computes addition on numerals" is reduced to the rule's soundness, argued here:
Lean4Lean's `HasPrimitives` argument, done once in the model rather than trusted per
environment. `Nat.div`, `Nat.mod`, `Nat.gcd` and the bitwise operations, whose definitions go
through fuel or well-founded recursion and whose rules ask for proofs instead, are the next
subsection.

Conventions of the arguments: `n̄` is `lit n`, `N`, `Z` and `S` are `nat_ty`, `nat_zero` and
`nat_succ`; `Γ ⊢ n̄ : N` for every `n` by `lit_zero`/`lit_succ` (the typing of a `deq`); an
equation over fresh variables is instantiated at literals by substitution (`IsDefEq.instN`,
the spec's `inst_df`; the equations are stated in extended contexts, so `f` must be closed
for the premises' `f` to be the lifting of the conclusion's `f`, which is why every
function the equations mention is required closed, directly or by its own relation);
`f ā ≡ f ā : Π N, N` from the typing premise and `ā : N`, so the congruence `app_df` turns
`b̄ ≡ e` into `f ā b̄ ≡ f ā e`. The `*_eqs_i` rules are definitional (a relation introduced
by its only rule) and need no argument; the `_i` premises' order is also the generator's.

| rule | argument |
|---|---|
| `nat_add_lit`: `add_eqs G f > badd a b c > ⟦ G ⊢ f ā b̄ ≡ c̄ : N ⟧` | by induction on `b`, `f ā b̄ ≡ (a+b)‾`: `f ā 0̄ ≡ f ā Z ≡ ā` (`lit_zero`, congruence, the first equation at `x := ā`); `f ā (b+1)‾ ≡ f ā (S b̄) ≡ S (f ā b̄) ≡ S (a+b)‾ ≡ (a+b+1)‾` (`lit_succ`, the second equation at `x := ā, y := b̄`, the hypothesis with congruence, `lit_succ` backwards). `badd` gives `c = a+b` (above). |
| `nat_sub_lit`, `nat_sub_lit0`: `sub_eqs G f p > badd c b a > f ā b̄ ≡ c̄`; `> badd a c b > f ā b̄ ≡ 0̄` | by induction on `b`, `f ā b̄ ≡ (a ∸ b)‾` (truncated subtraction): the step is `f ā (S b̄) ≡ p (f ā b̄) ≡ p (a∸b)‾`, and `pred_eqs G p` gives `p Z ≡ Z` and `p (S n̄) ≡ n̄`, so `p (a∸b)‾ ≡ (a∸b∸1)‾` in both cases. `c + b = a` makes `a ∸ b = c`, and `a + c = b` makes `a ∸ b = 0`. |
| `nat_mul_lit`: `mul_eqs G f fa > bmul a b c > f ā b̄ ≡ c̄` | by induction on `b`, `f ā b̄ ≡ (a·b)‾`: `f ā (S b̄) ≡ fa (f ā b̄) ā ≡ fa (a·b)‾ ā ≡ (a·b + a)‾`, the last by `nat_add_lit`'s argument for `fa` (its premise `add_eqs G fa`). |
| `nat_pow_lit`: `pow_eqs G f fm fa > bpow a b c > f ā b̄ ≡ c̄` | by induction on `b`, `f ā b̄ ≡ (a^b)‾`: `f ā 0̄ ≡ S Z ≡ 1̄` (`a^0 = 1`, as `bpow`); `f ā (S b̄) ≡ fm (f ā b̄) ā ≡ fm (a^b)‾ ā ≡ (a^b · a)‾` by `nat_mul_lit`'s argument for `fm`. |
| `nat_beq_lit`: `beq_eqs G f B t u > f ā ā ≡ t : B`; `nat_beq_lit_lt`: `> baddc a c b > f ā b̄ ≡ u`; `nat_beq_lit_gt`: `> baddc b c a > f ā b̄ ≡ u` | the fourth equation, `f (S x) (S y) ≡ f x y`, at literals (`lit_succ` on both arguments) gives `f (n+1)‾ (m+1)‾ ≡ f n̄ m̄`, so by induction on `a`: `f ā ā ≡ f 0̄ 0̄ ≡ f Z Z ≡ t`; for `b = a+c+1 > a`, `f ā b̄ ≡ f 0̄ (c+1)‾ ≡ f Z (S c̄) ≡ u` (the second equation at `x := c̄`); for `a = b+c+1 > b` symmetrically with the third. `B`, `t` and `u` are required closed because `u` occurs in equations stated under a binder (and `B` as their type); `t` is only used in `G`, so its closedness is a harmless extra premise. |
| `nat_ble_lit`: `ble_eqs G f B t u > badd a c b > f ā b̄ ≡ t`; `nat_ble_lit_gt`: `> baddc b c a > f ā b̄ ≡ u` | as for `beq` with the third equation: for `b = a+c`, `f ā b̄ ≡ f 0̄ c̄ ≡ f Z c̄ ≡ t` (the first equation at `x := c̄`); for `a = b+c+1`, `f ā b̄ ≡ f (c+1)‾ 0̄ ≡ f (S c̄) Z ≡ u` (the second). |
| `nat_shl_lit`: `shl_eqs G f fm fa > bpow 2 b p > bmul a p c > f ā b̄ ≡ c̄` | by induction on `b` for all `a`, `f ā b̄ ≡ (a·2^b)‾`: `f ā 0̄ ≡ ā`; `f ā (S b̄) ≡ f (fm 2̄ ā) b̄ ≡ f (2a)‾ b̄ ≡ (2a·2^b)‾` (the second equation, `nat_mul_lit`'s argument for `fm` with congruence, the hypothesis at `2a`). |
| `nat_shr_lit_z`: `shr_eqs G f fd > f ā 0̄ ≡ ā`; `nat_shr_lit_s`: `> bsucc b b2 > f ā b̄ ≡ c̄ > fd c̄ 2̄ ≡ c2‾ > f ā b2‾ ≡ c2‾` | one shift at a time, with the division by 2 a premise (the certificate derives it from `Nat.div`'s rule or axiom): `f ā 0̄ ≡ f ā Z ≡ ā`; `f ā b2‾ ≡ f ā (S b̄) ≡ fd (f ā b̄) 2̄ ≡ fd c̄ 2̄ ≡ c2‾` (`lit_succ`, the second equation at `x := ā, y := b̄`, congruence with the third premise, which needs `fd` closed and typed, both from the premises, then the fourth). Nothing else is assumed of `fd`. |

The equations are derived with the kernel's computation on literals switched off in nanoda
(`nat_ops_off`), since `Nat.beq 0 0 ≡ true` would otherwise be a computation about the very
rule being established; the derivation then unfolds the definition (which is what the
equations are about).

### The division-like operations (`spec/lean-lit.mm0`, "The division-like operations"; `lean0/src/natrec.rs`, `lean0/baked/`)

Lean defines `Nat.div` and `Nat.mod` by fuel recursion, and `Nat.gcd` and `Nat.bitwise` (with
`land`/`lor`/`xor`) by the well-founded fixpoint `WellFounded.Nat.fix`. Lean4Lean checks their
defining equations (`checkNatFuelRec`, `checkNatGcd`, `checkNatBitwise`), through `dite`/`ite`
on decided propositions. Until 2026-11-23 the spec stated those checks as relations over
variables for `dite`, `Decidable.intro`, `Nat.decLe`, the fuel functions and the proof terms
(eleven relations, up to 50 parameters). It now asks for something else: **proofs, in the
theory itself, of equations that determine the function**. A premise `⟦ₜ G ⊢ h : T ⟧`, with `h`
a variable of the relation's rule and not of the relation, says that the proposition `T` has a
proof. `nat_eq x y` is Lean's `@Eq Nat x y` (the block `eq_D`) and `nat_lt x y` is
`Nat.le (Nat.succ x) y` over the block `le_D`, Lean's `Nat.le` as the spec has it (compared with
the export's like `nat_D`; `lean0 check`).

| relation | proofs of |
|---|---|
| `divmod_eqs G fd fm fmul fadd` | with `mul_eqs G fmul fadd`: `y * (x / y) + x % y = x`, `0 < y → x % y < y`, `x / 0 = 0`, for `fd` as `/`, `fm` as `%` |
| `gcd_eqs G f fd fm fmul fadd` | with `divmod_eqs`: `f 0 y = y`, `f (x + 1) y = f (y % (x + 1)) (x + 1)` |
| `land_eqs`, `lor_eqs`, `xor_eqs G f fd fm fmul fadd` | with `divmod_eqs`: `f x y = f (x/2) (y/2) + f (x/2) (y/2) + bit`, where `bit` is `(x%2 + y%2) / 2`, `(x%2 + y%2 + 1) / 2`, `(x%2 + y%2) % 2` |

**Why a proof is enough.** The argument is semantic (it is the model's, §11, where these rules
are theorems): every closed function of type `Nat → Nat → Nat` has a value on numerals,
a proof of `Eq` exists only between equal values, and a proof of `Nat.le` at numerals only when
the first is at most the second. So the three facts of `divmod_eqs` hold of the values of `fd`
and `fm` at all numerals, with `fmul` and `fadd` multiplication and addition by `mul_eqs`
(`nat_mul_lit`, `nat_add_lit`). Syntactically the same conclusion needs canonicity, which the
spec does not otherwise rely on: a closed proof of `@Eq Nat a b` between numerals is
`Eq.refl`, so `a` and `b` are the same numeral. The rules are therefore stronger than
Lean4Lean's in one respect: they apply to any closed function with such proofs, not only to
one that unfolds like Lean's definition; what they conclude is true of every such function.

| rule | argument |
|---|---|
| `nat_div_lit`: `divmod_eqs G fd fm fmul fadd > bmul b q m > badd m r a > baddc r x b > fd ā b̄ ≡ q̄` | `b > r ≥ 0`, so `b ≥ 1`. The values `q' = fd ā b̄`, `r' = fm ā b̄` are numerals with `b·q' + r' = a` (the first proof at `x := ā, y := b̄`) and `r' < b` (the second, whose hypothesis `0 < b̄` has a proof). Quotient and remainder are unique, and the premises say `b·q + r = a`, `r < b`: `q' = q`. |
| `nat_div_lit0`: `> fd ā 0̄ ≡ 0̄` | the third proof at `x := ā`. |
| `nat_mod_lit`: `> (the same premises) > fm ā b̄ ≡ r̄` | as `nat_div_lit`: `r' = r`. |
| `nat_mod_lit0`: `> fm ā 0̄ ≡ ā` | the first proof at `y := 0̄`: `0·q' + r' = a`, so `r' = a`. |
| `nat_gcd_lit`: `gcd_eqs G f fd fm fmul fadd > bmul g p a > bmul g q b > bmul x a m > bmul y b n > badd n g m > f ā b̄ ≡ ḡ`; `nat_gcd_lit2` with `badd m g n` | By `divmod_eqs`, `fm` is the remainder at a positive divisor (as above). By induction on `a`, `f ā b̄` is `gcd a b`: `a = 0` is the first proof; for `a + 1` the second gives `f (b mod (a+1))‾ (a+1)‾`, and `b mod (a+1) ≤ a`. The premises make `g = gcd a b` (`g` divides both; `x·a = y·b + g` or `y·b = x·a + g` makes every common divisor divide `g`; `a = b = 0` forces `g = 0`). |
| `nat_land_lit`: `land_eqs G f fd fm fmul fadd > band a b c > f ā b̄ ≡ c̄`; `nat_lor_lit`, `nat_xor_lit` with `lor_eqs`, `bor` and `xor_eqs`, `bxor` | By `divmod_eqs`, `fd x̄ 2̄` and `fm x̄ 2̄` are `x div 2` and `x mod 2`. The recurrence determines `f` on numerals, by induction on `a + b`: at `0, 0` it reads `v = v + v + bit(0,0)` with `bit(0,0) = 0` for all three, so `v = 0`; otherwise the halves are smaller. The function it determines is the bitwise operation: its value has low bit `bit(a mod 2, b mod 2)`, which is the and, the or and the exclusive or of the two low bits, and the rest is the value at the halves. `band`, `bor`, `bxor` compute the same on binary numerals. |

**What the generator supplies** (`natrec.rs`, not trusted): the proofs are those of
`lean0/baked/Baked.lean`, written for Lean's definitions (Lean v4.35.0) and compiled by Lean;
`scripts/baked.sh` exports their proof terms (`baked.ndjson`, embedded in lean0), and the
elaborator types each like any proof term of the export, with the lemmas inlined, so the
premise is a derivation the verifier checks. The functions a definition does not depend on are
terms in the relation: the multiplication always (a `Nat.rec` over `Nat.add`, whose `mul_eqs`
holds by unfolding), and a copy of Lean's `Nat.mod` for `Nat.div`, of `Nat.div` for `Nat.mod`
and `Nat.gcd` (the copies are equal to the originals by unfolding, and the proofs are carried
over along that equality). An export therefore needs nothing beyond the operation, `Eq` and
`Nat.le`, which every one of these definitions depends on. The proofs of the three bitwise
recurrences use `propext`, as Lean's `Nat.bitwise` itself does (`Nat.bitwise_rec_lemma`); the
others use no axiom. A development whose `Nat.div` (say) is defined differently gets no proof
from lean0, and its literal divisions are then errors; the rules would accept its own proofs.

String literals have no axioms: a string literal is translated as its expansion
`String.ofList [Char.ofNat n, …]` (Lean4Lean's translation; nanoda expands it in `def_eq`), so
every step about one is an ordinary derivation.

## 6. Substitution and weakening

What is claimed for these rules (2026-11-26). `inst_df`, `weak_df` and `weak_base_df` are structural
rules of Lean0's judgment, on the same footing as the others: each is a theorem of the model
(§11), and that is the soundness claim. The arguments below show something else, which predates
the model: that each is the transcription of a theorem Lean4Lean proves about *its* judgment
(`IsDefEq.instN`, `IsDefEq.weakN`), where the rule is admissible, that is, adds nothing
derivable. Admissibility is not proved for Lean0's axioms, whose inductive types, quotients and
literals are stated differently, and nothing here depends on it; it bears only on how closely
Lean0's derivable judgments match Lean4Lean's, which the literal rules of §5 already exceed.

### `cinst` (`spec/lean.mm0`, "Contexts")

| MM0 | interpreted as |
|---|---|
| `cinst k G0 A0 a G1 G` | `Ctx.InstN G0 a A0 k G1 G` (Typing/Lemmas.lean:86) |

`cinst_z` and `cinst_s` are its two constructors, transcribed: `zero : Ctx.InstN 0 (A₀ :: Γ₀)
Γ₀` and `succ : Ctx.InstN k Γ Γ' → Ctx.InstN (k+1) (A::Γ) (A.inst e₀ k :: Γ')`, with the
`inst` relation for `A.inst e₀ k`. Context entries are types relative to their tail, as in
Lean4Lean's list contexts (`Lookup` lifts on the way out), so the substitution depth of the
entry `k` places above `A₀` is `k`, as in the constructor. `Γ₀`, `e₀` and `A₀` are arguments
of the MM0 relation where Lean4Lean has them as parameters of the inductive.

### `inst_df` (`spec/lean.mm0`, "Structural rules")

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

### `cext` (`spec/lean.mm0`, "Contexts")

| MM0 | interpreted as |
|---|---|
| `cext n G G2` | `Ctx.LiftN n 0 G G2` (Typing/Lemmas.lean:8-10) |

Only the `zero` constructor, `Ctx.LiftN n 0 Γ (As ++ Γ)` with `As.length = n`: `cext_z` and
`cext_s` build `As ++ Γ` one entry at a time, counting `n`. Every derivable `cext n G G2` has
`G2` equal to `G` with `n` entries (any expressions) consed on, which is the constructor's
instance with `As` those entries; `Ctx.LiftN.zero` puts no condition on `As`.

### `weak_df` (`spec/lean.mm0`, "Structural rules")

`deq G e e2 A > cext n G G2 > lift n nz e r > lift n nz e2 r2 > lift n nz A R > deq G2 r r2 R` is
`IsDefEq.weakN` (Typing/Lemmas.lean:501) for `W : Ctx.LiftN n 0 Γ Γ'`: from `henv :
env.Ordered` and `H : env.IsDefEq U Γ e1 e2 A` it concludes `env.IsDefEq U Γ' (e1.liftN n)
(e2.liftN n) (A.liftN n)`. The `lift` premises pin `r`, `r2`, `R` (functionality, §1). The
argument is the one for `inst_df`: the rule is valid in the standard model, so it needs no check
against the generated axioms, and its one assumption, `env.Ordered`, is the one `inst_df` and
the stage-A axioms already rest on. The generated rules are all schematic in `G` (a context
appears only as the variable `G` of their premises and conclusion), as the model's constant
rules are, so nothing in them depends on the context's length.

### `weak_base_df` (`spec/lean-ind.mm0`, Part III, before `ind_iota_eq`)

`deq G e e2 A > pis G (srt lz) K > closed nz K > clen G k > closed k e > closed k e2 > closed k A >
capp G G0 G2 > deq G2 e e2 A`, where `G2` is `G` appended to a base context `G0`: a judgment in a
closed context holds over any base context. It is `IsDefEq.weakN` again, for `W : Ctx.LiftN n k Γ Γ'`
at `k` the length of `G` and `n` the length of `G0` (the new entries go below all of `G`): the
entries of `G` are lifted at their own depths and `e`, `e2`, `A` at `k`, and lifting a term closed
below the cutoff is the identity. The premises say exactly that: `closed nz (Π G, Prop)` is each
entry of `G` closed over the entries before it (`pis` builds the telescope's type), and `closed k`
of the three terms. `weak_df` cannot express it (it adds entries above, `Ctx.LiftN n 0`), and a
closed judgment proved by a rule that fixes its whole context (`ind_iota_eq`, §4) is otherwise
unusable inside another context. In the reduction the rule is a theorem (`mweak_base_df` for every
hook, `spec/tg/model/model-ci.mm0`, §11): a valuation of `G2` begins with a valuation of `G`
(`weak_base_sem`), at which the three terms have the same values.


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
`goCache_Inv_of_Inv._mutual`, `std.part62bbbbbbb.mm0`.

## 8. From the certificate to Lean: the statement checker

The verifiers establish that the certificate proves its `.mm0` statements. What ties those
statements to the Lean declarations is `lean0 check EXPORT STATEMENTS.mm0...`
(`lean0-check/src/statements.rs`, about 470 lines with comments; the `lean0-check` crate does
not depend on the generator), written independently of the generator: it
uses only nanoda's export parser and expression type, and parses the generated `.mm0` text
itself, accepting only the forms lean0 writes. For every declaration of the export it checks:

* exactly one MM0 term claims to stand for it (the doc comment "Lean ... `NAME`"), taking one
  level variable per universe parameter, and no term claims a constant the export lacks; or
  it is a type, constructor or recursor of a stage-B block, which stands as
  `ind_ty (X_D us) i`, `ind_ctor (X_D us) i c` or `ind_rec (X_D us) i v` (the names from the
  export's `all` and constructor lists and `X.rec`, and `X.rec_k` for the recursor of the
  `k`th auxiliary type of a nested block; a recursor with the motive's level first when the
  export's has one more level than the block's; an auxiliary type or its constructor stands
  for nothing, so a statement about one is no type claim);
* a block's data definition `def X_D (us): ind = ind_mk X_blk P T N` (doc "The inductive block
  of `X`...") is the export's declaration: `P` has the declared number of parameters, each
  type's type is `Π P, F_i` and each constructor's `Π P, K` with the block's types as
  variables above the parameters, compared with the exported types after their binders'
  type annotations (`outParam`, `optParam`, ...) are consumed as the kernel does (§4); for a
  nested block (`N` not empty), `T` has the declared types and then as many auxiliary
  types as `N` has occurrences, and each declared type's constructor types are compared
  restored: an auxiliary type `#(d + np + n0 + k)` applied to exactly the parameters (else
  the block is reported) and to further arguments becomes occurrence `k` lifted to depth
  `d`, applied to those arguments (§4, `rst`). The auxiliary types' own data is not compared
  (nothing in the export states it): the spec's `nst_ok` checks it against the occurrences,
  and an occurrence list other than the kernel's gives the recursors other types than the
  export's, which the type claims below catch;
* every statement giving that term's type, `ty G (c us) T` or the `constDF` axiom
  `deq G (c us) (c us2) T`, has `T` equal to the declaration's type, read back into Lean (de
  Bruijn indices, sorts and levels, constants with their levels, projections by structure and
  index, Nat literals; binder names and styles are not compared; a `let` is inlined and a
  string literal expanded, as the translation does);
* a theorem's and a definition's type is stated by a proved theorem, not an axiom;
* a definition's body is its value;
* the spec's own declarations of Lean constants (the statements between the spec's
  `lean0-check` marks: the blocks `nat_D`, `eq_D`, `le_D` and the others stated there, and the
  quotient primitives `quot`, `quot_mk`, `quot_lift`, `quot_ind`) stand for `Nat`, `Eq`,
  `Nat.le`, ..., `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` when the export declares them, and are compared the same way (a spec
  declaration the export lacks is ignored);
* an opaque constant is `def c (us): expr = $ cst A (lcons u1 ... lnil) $` over its own
  levels in order, with `A` a `term A: atom` that no other definition uses (a shared or
  aliased atom would make two constants equal by `eeqv_cst` and `eeqv_df`);
* an axiom concluding `closed` or `eeqv` about a constant has the syntactic shape of §4:
  `closed k (c us)` over `(k: nat)` and the levels, or `leqv u u2 > ... > eeqv (c us) (c us2)`
  over the levels and their primed copies, with no other hypotheses;
* every `term` the certificate declares is a constant of sort `atom` (an opaque constant's)
  or `blk` (a block's), the sorts §11's encoding leaves open.

Not checked by it: whether a
theorem's proof term (an abstract def) is the export's (it is never stated, so it cannot
matter). The comparison reads both sides structurally, so a translation bug, a doc comment
naming the wrong constant, or a statement edited by hand is reported, with the first place
the two differ. All of Init (59,423 declarations, 181,310 statements with the schema, the 32
parts' own `.mm0` files) passes in 16 s; `scripts/test.sh` checks that edited statements are
rejected.

After the check, `lean0 check` lists the export's top-level declarations (theorems,
definitions, opaques and axioms that no declaration of the export mentions; for a slice
`lean4export MOD -- NAMES`, the named ones) with their Lean types, from nanoda's pretty
printer (`lean0-check/src/summary.rs`). The list is for the person reading the result and
plays no part in the check: what is checked is every declaration, as above.

## 9. Notations in the spec (2026-10-30)

`spec/lean.mm0` declares notations, and its formulas are written with them: `⟦ G ⊢ e ≡ e2 : A ⟧`
for `deq G e e2 A`, `⟦ₜ G ⊢ e : A ⟧` for `ty G e A`, `λ A, e` and `Π A, B` for `lam` and `pi`,
`f @ a` for `app`, `#i` for `bvar`, `A :: G` and `[]` for `cons` and `nil` (contexts are
written `G ▷ A` since 2026-11-23, below), `a ⊔ b` for
`lmax`, and `≤`, `<` and `≈` for `le`, `lt` and `leqv`. Each has an ASCII form as well,
declared first (the scheme is at the end of this section);
the Unicode form is declared last. The delimiters are `( ) , #`.
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

Numerals (2026-11-03): `0` is a notation for `nz`, and `1` to `9` are notations for the
definitions `n1` (`s 0`) to `n9` (`s 8`); `#` became a delimiter, so `#3` is `bvar 3`. Unlike
the notations above this changes the statements: a formula with `#3` mentions the definition
`n3` where it mentioned `s (s (s nz))`. A definition is an abbreviation, which the verifiers
unfold (a `def` is conservative, `mm0.md`), so each statement is equivalent to the old one, and
the generator proves the old forms and converts. Expanding every numeral back into a chain of
`s` (and `#3` into `# 3`) gives back the old text character for character. The statements of
the `lean0-check` block stay in prefix form, as the statement checker reads them.

Infix turnstiles (2026-11-05): the judgment was `⊢ G, e ≡ e2 : A` and typing `⊩ G, e : A`. MM0
requires a notation to begin with a constant unique to it, so `G ⊢ ...` cannot be a notation
(both verifiers reject such a formula), and each judgment form now has its own bracket. The
terms are unchanged, so the statements are too: the spec's math tokens, apart from the
judgment's marks, are the same in the same order, and the certificates in `build/gen/` at the
time (`annot`, `congtype`, `core`, `deflevels`, `handlecycle`, `illegal`, `induct`,
`initsample`, `lit`, `nested`, `projhandle`, `propproj`, `weakhandle`) verify with both
verifiers against the new text, and again after the quotient and literal axioms, which were
still in prefix form, were rewritten in the notations. The same text with every judgment in the ASCII form verifies
as well (on `core`), while one with the two sides of `beta`'s conclusion swapped is rejected.
The generator's parser reads the new text as the old: regenerating with it gives byte-identical
`.mmb` files.

`Prop` (2026-11-05): `Prop` is the definition `srt lz`, and the spec's formulas use it. Like the
numerals this changes the statements, not their content: a definition is an abbreviation, and
expanding `Prop` gives back the old formulas (up to parentheses). The generator proves the old
forms and converts, which costs about 0.01% in certificate size. The block between the
`lean0-check` marks keeps `srt lz`, in prefix form.

`ℕ` (2026-11-05) is a notation for the definition `nat_ty`, so its terms are unchanged.

Typing premises (2026-11-05): the core rules `bvar_ty`, `beta`, `eta`, `proof_irrel`, `inst_df` and
`inh_i` now state typing with `ty`, the definition of `⟦ G ⊢ e ≡ e : A ⟧`, where they spelled
out the diagonal as Lean4Lean does. The statements are equivalent by unfolding. The generator
converts at each use, which costs 0.38% on `Init.Prelude`.

Arithmetic as equations, and `Sort` (2026-11-22): the relations read as sums and products are
written as equations in brackets, `⦃ i + n = j ⦄` for `add i n j` on the unary numerals and, on
the binary ones, `⟪ a + b = c ⟫` for `badd`, `⟪₁ a + b + 1 = c ⟫` for `baddc`, `⟪ₛ a + 1 = b ⟫`
for `bsucc`, `⟪₂ 2 * a = b ⟫` for `bdbl`, `⟪ₘ a * b = c ⟫` for `bmul`, `⟪ₚ a ^ b = c ⟫` for
`bpow`, and `⟪ₐ a &&& b = c ⟫`, `⟪ₒ a ||| b = c ⟫`, `⟪ₓ a ^^^ b = c ⟫` for `band`, `bor`, `bxor`; each relation has an opening bracket
of its own because a notation must begin with a constant unique to it, and the `1` and `2` in
the notations of `baddc`, `bsucc` and `bdbl` are tokens of the notation, not arguments. `Sort u` is a prefix notation for `srt u`. The terms are unchanged, so
the statements are too: the certificates in `build/gen/` made before the change (`induct`,
`lit`, `nested`) verify with both verifiers against the new text, and the set-theoretic
encoding generated from the spec (`scripts/tg-lean.py --check`, which reads the notations with
its own parser) is byte for byte the same. The block between the `lean0-check` marks keeps the
prefix form.

Substitution, lifting and lookup (2026-11-23), in the same manner: `⟮ [ #k ↦ a ] e = e2 ⟯` for
`inst k e a e2`, `⟮ₗ [ #k ↑ n ] e = e2 ⟯` for `lift n k e e2` (the variables from `#k` up raised
by `n`), `⟮ₖ G ∋ #k : A ⟯` for `lookup G k A`, and at levels `⟮ᵤ [ n ↦ a ] l = l2 ⟯` for
`lsubst n l a l2`. The `#` before `k` is a token of the
notation (the delimiter that also writes a bound variable), not an application of `bvar`: the
argument is the number `k`. Checked as before: a certificate made before the change (`induct`)
verifies with both verifiers against the new text, in both modes, and `scripts/tg-lean.py
--check` passes unchanged.

Contexts left to right, and the lift at cutoff 0 (2026-11-23): two definitions with notations.
`G ▷ A` (`snoc G A`, ASCII `G |> A`) is defined as `A :: G`, and contexts are written with it,
so a context reads in the order of its binders, each type to the right of the variables it
mentions (`[] ▷ Sort u ▷ (Π #0, Π #1, Prop)` for `α`, then `r : α → α → Prop`); `#0` is the last
entry. An infix notation cannot exchange its arguments, hence the definition. The lists that
are not contexts (the nested occurrences) keep `::`. `⟮₀ e ↑ n = e2 ⟯` (`lift0 n e e2`) is defined as `⟮ₗ [ #0 ↑ n ] e = e2 ⟯`. As with the numerals and `Prop`,
definitions change the statements but not their content: unfolding the two gives back the old
formulas. Checked by the encoding, which unfolds the spec's definitions: the classes of clauses
that `scripts/tg-lean.py` generates from the new text (and every `lrel_A` statement) are those
generated from the old one, and the model's proofs are unchanged. (A certificate made before
does not verify against the new text, since a certificate restates the spec's statements.) The
generator proves, once per certificate and rule it uses, a lemma that states the rule with the
definitions unfolded, and works with the unfolded forms; certificates grow by 0.1 to 0.4%.
`lean0 modes` reads the clauses with the two definitions unfolded.

The generated statements keep the prefix form (`deq G e e2 A`), which MM0 allows for every
term with or without a notation; the statement checker reads only that form. One notation
token looks like an identifier (`[a-zA-Z_][a-zA-Z0-9_]*`): `Sort`. A verifier reads such a token
as the notation wherever it stands, while the statement checker, which reads prefix form, would
take it for a name. So the checker reports a statement whose name or bound variable is an
identifier-like notation token of the spec (it collects them from the spec's declarations; a
negative test in `scripts/test.sh`), and the generator never makes such a name. No other token
can collide with a generated name.

One scheme for the spec and the set theory (2026-11-25). The spec's notations and those of
`spec/tg` are declared to live in one MM0 environment, so that the model states each rule in the
spec's own notation (`spec/tg/model/model-top.mm0`; `scripts/tg-lean.py` writes the spec's
notation declarations into the encoding and prints the statements, and refuses a model statement
that differs). MM0 fixes what that takes: a notation is chosen by its first token alone, a token
that follows a variable has one precedence everywhere, and a precedence level has one
associativity. The conventions:

- A family of related notations has one pair of brackets, and a subscript on the opening bracket
  names the member; the commonest member has none. Judgments: `⟦ G ⊢ e ≡ e2 : A ⟧` and typing
  `⟦ₜ G ⊢ e : A ⟧` (before: `⟨ ⟩`, which is the set theory's ordered pair). Substitution and
  lifting `⟮ ⟯`, binary arithmetic `⟪ ⟫`, index arithmetic `⦃ ⦄`. Telescopes `⌊ ⌋`: `⌊| G | = n ⌋`
  (`clen G n`), `⌊ G ++ P = G2 ⌋` (`capp P G G2`: `G` followed by the entries of `P`),
  `⌊Π P, b = T ⌋` and `⌊λ P, b = T ⌋` (`pis`, `lams`; ASCII `<_| G | = n _>`, `<_ .. _>`,
  `<_\Pi`, `<_\`). In the set theory: functions
  `⌈ F : A → B ⌉` (`fn_into`; `⌈₁` for an injection), satisfaction `⟅ A , S ⊨ C ⟆` (readback).
- A substitution is written before its term, in square brackets, on both sides:
  `⟮ [ #k ↦ a ] e = e2 ⟯` in the spec, `[ x / t ] p` in the set theory (`[[ x / t ]] A` at
  classes, which had `⟦ ⟧`). `[ ] / |` are no longer delimiters of `tg.mm0`, so a substitution
  is written with spaces and the spec's `[]` remains a token.
- Binders take a comma, `λ A, e` and `Π A, B`, and the set theory's are `λₛ x ∈ A, B` (`clam`)
  and `Πₛ x ∈ A, B` (`cpi`). The spec's delimiters are `( ) , #`.
- Precedences: `=` 50, `+` 64, `*` 70, `^` 75 wherever they occur; `::` 59 and `▷` 63 (they
  were 60 and 62, levels where the set theory associates the other way); the spec's `λ` and `Π`
  55 (they were 20), so that one may stand before an `=` without parentheses
  (`⟮ₗ [ #k ↑ n ] λ A, b = λ A2, b2 ⟯`): no operator of the spec's terms lies between.
- In the set theory, sequences are `a +: S` (`scons`) and `S :+ a` (`ssnoc`), so a tree of the
  encoding reads `⟨ kc_app , enc_expr a1 +: enc_expr a2 +: ∅ ⟩`, and arithmetic on `ω` is
  `a + b`, `a · b`, `a ^ b` (`nadd`, `nmul`, `npow`).
- Every notation has an ASCII form, declared first: the opening bracket is `<` and a character
  for the family with the subscript as a suffix, the closing bracket is mirrored
  (`<: G |- e == e2 : A :>`, `<:t`, `<~ [ #k := a ] e = e2 ~>`, `<~l`, `<~0`, `<~k`, `<~u`,
  `<< a + b = c >>`, `<<1`, `<<s`, `<<2`, `<<m`, `<<p`, `<<a`, `<<o`, `<<x`, `<+ i + n = j +>`,
  `<@ F : A -> B @>`, `<@1`, `<. a , b >.` for the pair; `\ A, e`, `\Pi A, B`, `\s x e. A, B`, `\Pis`, `|_|` for `⊔`,
  `\N` for `ℕ`).

No term changed, so no statement did. Checked: `scripts/tg-lean.py --check` on the rewritten
spec gave the committed encoding byte for byte before the encoding's own text was touched; a
certificate made before the change verifies against the new text with both verifiers, in both
modes; all 6,971 declarations of the set-theory chain state the same terms as before
(`historical/tg-ngram/same.py` on the two joined texts); and the chain verifies (5542 theorems
over 130 axioms).

## 10. The encoding: how the spec departs from Lean4Lean's presentation

The spec transcribes Lean4Lean's `IsDefEq` rules over de Bruijn terms (`VExpr`) as closed
first-order MM0 terms: sorts `nat` (indices), `lvl`, `expr` and `ctx`; the judgment
`deq G e e2 A` (`⟦ G ⊢ e ≡ e2 : A ⟧`); and the side relations `lift`, `inst`, `lookup` and
`closed`, with one axiom per defining clause, which the generator proves syntax-directed.

The spec is four files (the core, then inductive types, quotients and Nat literals, each
adding its expression constructors with their clauses of the core's relations), and each
file is in three parts (the core's header); below, Part I means the files' Parts I together,
and likewise Parts II and III. Part I, *Syntax*, declares the sorts and the
relations that are functions or predicates on syntax, defined by clauses recursing on their
inputs; nothing in it mentions `≈` or `⊢`. Part II declares `≈` and `⊢` and the relations
defined over them in the same way (the well-formedness of a block, its elimination level, the
defining equations of the literal operations). Part III states the rules: the 76 axioms
concluding `≈` or `⊢` (and `inh_i`), which are the semantic content and the only axioms whose
truth is at issue in §§2–6; the other 316 are definitions, which `lean0 modes` checks to be the
functions and predicates they are read as (§4, *Functionality*). In a reduction to set theory
the sorts become inductive sets, the clauses of Parts I and II the defining equations of
functions given by the recursion theorem, and Part III the theorems to prove of the model.

The departures from the verbatim presentation:

* **No environment term.** Lean4Lean's `VEnv`, with the `constDF` and `extra` rules, is
  replaced by one MM0 declaration per Lean constant, whose arguments are the constant's
  universe parameters as `lvl` variables. A definition or theorem `c.{u v} : T := v` becomes
  `def c (u v: lvl): expr = $ v $;` with a proved typing theorem `⟦ₜ G ⊢ c u v : T ⟧`, schematic in
  `G`; so δ-unfolding is MM0 unfolding, and universe instantiation (`instL`) is MM0
  substitution of the `lvl` variables. A theorem's body is abstract (only in the MMB), so the
  `.mm0` never shows a proof term, and so is an opaque constant's value. Lean's axioms become an atom and a definition,
  `term c_atom: atom; def c (u v: lvl): expr = $ cst c_atom (lcons u (lcons v lnil)) $;`
  (the spec's `cst`: an atom at a list of levels, closed and level-congruent by the spec's
  `closed_cst` and `eeqv_cst`), with one generated axiom each, a `constDF` instance
  (`deq G (c us) (c us2) T` under `leqv` premises on the levels); `closed k (c us)` is a
  theorem. In the model an atom is interpreted by an environment parameter (a function of
  the levels' values), and nothing in the spec tells two atoms apart.
  Soundness: an environment whose definitions are inlined proves the same judgments as the
  original (this is Lean4Lean's `extra` treatment of `c ≡ value : T`). That adequacy argument is
  on paper; a Lean proof over Lean4Lean's `VEnv` would close it.
* **Level variables are MM0 variables**, so `U` and `l.WF` disappear and every level axiom must
  hold schematically (§2). With the case-split rules of §4 (`lparam`, `leqv_cases`,
  `leqv_inst`) the axioms decide `leqv` completely: `imax`-free levels are compared by normal
  form, and a parameter under `imax` is split on until none is left.
* **Nat literals** (§5): `lit : bin > expr` over binary numerals, tied to `Nat.zero` and
  `Nat.succ` by the spec (`lit_zero`, `lit_succ`), with the accelerated operations as rules
  over their defining equations (`add_eqs`/`nat_add_lit`, ...), or for the division-like
  ones over proofs of characterizing equations (`divmod_eqs`, `gcd_eqs`, `land_eqs`, ...). A **string literal** is translated as its `String.ofList` expansion and
  needs no axiom.
* **Inductives** (§4, stage B): a block is a data term, `def X_D (us): ind = ind_mk X_blk P T N`,
  and its types, constructors and recursors are the spec's `ind_ty (X_D us) i`,
  `ind_ctor (X_D us) i c` and `ind_rec (X_D us) i v` (no term per constant; `v` the motive's
  level, `lz` for a small eliminator). The certificate proves `tys_ok G (X_D us)` and
  `ind_wf G (X_D us)`, and from the schema the typing lemma `X_df` of each constant (at any
  equivalent levels, by `eeqv_df`), each recursor rule's iota lemma `X_rec_c_iota` (with the
  exported rule value as a public `def`, checked to be the schema's `rec_rhs`), and for a
  structure the projection and eta lemmas.
  A nested block is the mutual block the kernel checks in its place, with
  the occurrences `N` restored in what it states (§4).
* **Projections and structure eta** (§4): the spec's `proj b i e` for every structure, with
  the block's atom `b` (so that two structures' rules never apply to the same term) and the
  structural `closed`/`lift`/`inst` rules in the spec; typing, reduction and eta are lemmas
  of the schema.
* **`let`** is inlined during translation (derivations memoized on the DAG), and `mdata` is
  erased. Binder names and styles are not represented.

The generated `.mm0` therefore contains, per declaration, its `def` or `term` (or, for a
stage-B block, its atom and data definition), its typing statement, and for Lean's axioms
the atom and the `constDF` axiom (and the theorem `c_eeqv` when a block's data mentions a
theorem or opaque constant at its levels), plus the per-structure and per-recursor lemmas or axioms above;
lemmas made while proving are local to the MMB. §8 says how those statements are tied back
to the export.

## 11. The syntax encoding in set theory (`spec/tg/encoding/lean-tg.mm0`; argued here, to be re-audited)

The reduction of the spec to Tarski–Grothendieck set theory (`spec/tg/`) reads every sort of
the spec as a set of finite trees. `spec/tg/encoding/lean-tg.mm0` is generated by `scripts/tg-lean.py`
from `spec/lean.mm0` (`--check` fails when it is out of date). The generator reads the spec's
declarations in the order of `scripts/tg-order.txt`, not the order of the spec's files: the
labels and the order of each relation's clauses follow it, and the model's proofs depend on
them (no statement does: the order chooses among equivalent encodings). It imports the library
(`all.mm0`, whose only axioms are those of `tg.mm0`) and declares the spec's sorts and
constructors verbatim, without notations: every `term` of the spec whose sort is not `wff`,
42 of them (`nat_blk`, `eq_blk`, `le_blk` and the seven atoms of the quotient primitives and Lean's three axioms included). It also defines a
natural-number label for each sort (`ks_S`) and each constructor (`kc_c`), each label the
successor of the one before, and the signature `lsig`, one entry
`⟨ kc_c , ⟨ ks_S , args ⟩ ⟩` per constructor, with `args` the sequence of its argument
sorts' labels. The open sorts are `lopen = {ks_blk, ks_atom}`. The definitions `sorted`
and `ofsort` (library file `sorts.mm0`) make `ofsort lsig lopen ks_S` the least set of
trees closed under these rules:

- a constructor `c` of sort `S` with argument sorts `S1 … Sn` builds
  `⟨ kc_c , (t1, …, tn) ⟩` from trees `ti` of sort `Si`;
- every `⟨ n , ∅ ⟩` with `n ∊ ω` is a tree of an open sort.

The axioms, the file's only ones:

- per sort `S`, a term `enc_S: S > class`, and the axiom
  `enc_S_sorted (e: S): _ ⇒ enc_S e ∈ ofsort lsig lopen ks_S`;
- per constructor, its equation, e.g.
  `enc_app (a1 a2: expr): enc_expr (app a1 a2) ≐ ⟨ kc_app , scons (enc_expr a1) (scons (enc_expr a2) ∅) ⟩`,
  enrolled as a rewrite rule.

**Soundness (conservativity over the library).** Take any model of the library. Interpret
each sort `S` of the spec as the set `ofsort lsig lopen ks_S` of that model, each constructor
as building its node, and each `enc_S` as the identity. MM0 sorts must be nonempty, and
each of these sets is: `nz`, `lz`, `lnil`, `bvar nz`, a leaf, `nil`, `b0`, `nat_blk`,
`ind_mk nat_blk nil tnil`, `tnil` and `cnil` give an element of each. Under this
interpretation:

- a constructor maps trees of its argument sorts to a tree of its sort (the first rule
  above), so it is a well-defined operation on the interpreted sorts;
- each equation holds by definition;
- each sorting axiom holds because every element of the interpreted sort is in the set.

A constant that a later text adds to an open sort (`term X_blk: blk`, `term X_atom: atom`) is
interpreted as any leaf. The spec states no equation for it, and nothing tells two such
constants apart, so any choice is sound. A later text that adds a constructor to a sort
that is not open would break the sorting axiom, so §8's checker rejects a certificate's
`term` unless it is a constant of sort `atom` or `blk` (`lean0 gen` declares no other).

**What is deliberately absent.** There is no injectivity or disjointness axiom. MM0 cannot
state the syntactic equality such an axiom would conclude, and the reduction never needs
it: the relations of Parts I and II become definitions over the encodings (below), so
whatever a proof needs about them, such as the determinacy of a computing relation, is a
theorem about encodings, and equality of encodings is all it uses. Distinct labels make
distinct constructors' trees distinct inside set theory. There, that is a theorem about
`lsig` (`ofsort_S_cases`), not an axiom.

**The relations of Part I add no axiom.** The rest of `lean-tg.mm0` is definitions and
theorems. Each relation `R` of Part I gets a label `kr_R`, and its atoms are
`ra_R t1 … tn = ⟨ kr_R , (t1, …, tn) ⟩`. Each clause axiom `A` of Part I gets the class
`cl_A` of its ground instances `⟨ premises , conclusion ⟩` at all sets, with constructors
written as their trees and the spec's definitions unfolded. All of them, cut down to
`latoms = ω × fseq (trees ω)`, form one program `lprog`, and `lrel` is its set of derivable
atoms: the least fixed point of the program's step (library file `horn.mm0`). Each relation
is then a definition,
`def lift (a1 a2: nat) (a3 a4: expr): wff = $ _ ⇒ ra_lift (enc_nat a1) … ∈ lrel $`. The
spec's definitions follow verbatim, in prefix form. Each of the spec's 226 clause axioms of
Part I is restated as a theorem with the same name and statement. Theorems about the
program follow, also proved: per relation, that a clause of the program concluding an
`R`-atom is one of `R`'s (`lprog_R_pr`) and inversion (`lrel_R_cases`: a derivable atom is
an instance of one of its clauses, with the premises derivable); and the determinacy of the
computing relations that later proofs need (`lrel_R_det`).

`scripts/tg-lean.py --parse-check` writes every axiom of the spec, as the generator prints
it in prefix form, as a theorem proved by that axiom, and `scripts/test.sh` verifies this.
So the restated statements are the spec's.

**Part II's relations over level equivalence** (`spec/tg/encoding/lean-tg2.mm0`, 2026-11-10, generated
by the same script and checked by the same `--check`). The eight relations of Part II whose
clauses need only Part I's relations and `leqv` (`eeqv`, `lseqv`, `ind_eqv`, `ceqv`, `teqv`,
`cseqv`, `ulevel`, `nst_group`; the script finds them) are a second program of the same form
over Part I's least model: a clause's premises of these relations are its premises, and its
other premises are side conditions of its ground instances (an atom of Part I in `lrel`, two
level trees with equal values at every valuation, `lveq`, which is `leqv` at encodings). Each
relation is a definition (its atom is in `lrel2`, the least model), and each of the 29 clause
axioms is a theorem with the spec's statement, followed by `lprog2_R_pr` and inversion
`lrel2_R_cases`. No axioms.

**Part II's relations over the judgment** (`spec/tg/encoding/lean-tg3.mm0`, 2026-11-11, generated and
checked likewise). The other 35 relations of Part II (`sty`, `cwf`, `ind_wf`, `nst_ok`,
`large`, `proj_ok`, the literal relations `*_eqs`, ...) have premises of the
judgment `deq`, which is a term until the model defines it. They are a third program of the
same form over a parameter `J`, a class of judgment atoms standing for `deq`: their side
conditions are atoms of Part I in `lrel`, atoms of the second stratum in `lrel2`, `lveq`, and
judgments in `J`. Each relation is a definition `R_j J`, each of the 44 clause axioms a
theorem `A_j` for every `J` (the spec's statement with `deq` read as `deq_j J`), followed by
`lprog3_R_pr` and inversion `lrel3_R_cases`. The clauses' trees name the spec's large closed
constants (`nat_D`, `nat_ty`, `nat_zero`, `nat_succ`, `le_D`) by definitions `tr_D`, and each of the spec's definitions of
terms has a theorem `enc_D` giving its encoding. No axioms. The spec's relations and their clause axioms stay in the
rest file until the judgment is defined, when they become `R_j` at the judgment's atoms.

**Parts II and III** (`spec/tg/lean-tg-rest.mm0`, generated by the same script and checked by
the same `--check`). It imports the model (below) and states the rest of the spec as the spec
states it, in prefix form, with variables named like a library term renamed: Part II's
relations and their clauses and Part III's rules, less what the model declares (a spec term
as a definition, an axiom as a theorem; `lean0 tg-link` checks that each is the spec's
statement). Until 2026-11-20 that was 38 terms, 1 definition and 105 axioms. Since the
assembly (`model-top.mm0`, below) it is only the import of the model: every term of Parts
II and III is a definition of the model and every axiom a theorem. The trusted base in TG
mode (below) is `tg.mm0`'s 77 axioms and the 53 encoding axioms above, in place of the
spec's 372, with one new term and no axiom about it: the environment `Env` of the opaque
constants (below).

**The model** (`spec/tg/model/model-levels.mm0`, `spec/tg/model/model-den.mm0`, 2026-11-09, layer C of
the reduction; `spec/tg/model/model-meta.mm0` and `spec/tg/model/model-core.mm0`, 2026-11-10, layers D and I; it imports the strata `lean-tg2.mm0` and
`lean-tg3.mm0` after `model-levels.mm0`). Definitions and theorems only: no axiom, so nothing here is trusted beyond
`tg.mm0` and the encoding. What it changes in TG mode is the reading of the spec's `leqv`,
which is now a definition: a level valuation is a function from `ω` to `ω` (`lvals`), each
level's value is computed by structural recursion on its tree (`lv`: `lz` is 0, `ls` adds
one, `lmax` is `max`, `limax a b` is 0 when `b` is 0 and `max` otherwise, a parameter is
the valuation's value), and `leqv l l2` says the values agree at every valuation. The spec's
16 level rules (21 until 2026-11-26) are theorems about this definition (`leqv_cases` and `leqv_inst` through the
semantics of `lsubst` and `linst`, by induction on the trees). Replacing an axiomatized
relation by a definition that satisfies its axioms is conservative for statements that only
use the axioms, and the certificate's proofs only use them.

The rest of the model is not yet the spec's `deq`, so it changes nothing that is trusted:
- **The denotation** (`dt u M T w r`) is relative to an *admissible universe* `u`, a
  universe containing every `U_n`. A valuation of the de Bruijn variables is a finite
  sequence of elements of `u`, so the valuations form a set and the denotation is defined
  by structural recursion on the trees, like the levels. A semantics over all valuations
  would be a recursion whose values are proper classes. Every expression denotes an
  element of `u` (`den_in_u`), so extending a valuation by a typed term's value stays inside
  `u`. Admissible universes exist (`uadm_exists`).
- **A hook `M`** gives the value of the constructors whose meaning is the work of later
  layers: constants (the quotient primitives among them), literals and the inductive constants
  (`kexa`). It sees the universe, the label, the children and their values. Its value is the
  same at every valuation of the de Bruijn variables, so these constants are closed by
  construction, and it is cut to `u`.
- **The judgments** `mdeq M`, `minh M` quantify over every admissible universe, level
  valuation and satisfying valuation. Symmetry, transitivity, conversion, `sort_df`, `lam_df`,
  `pi_df`, `proof_irrel` and `inh_i` are theorems for every hook (`mdeq_symm` .. `minh_ty`).
  The spec's `deq` becomes `mdeq` at the hook the later layers define.
- **The metatheory of the syntax** (`model-meta.mm0`) relates the spec's `closed`, `lift`
  and `inst` to the denotation, for every derivable atom (the admissible clauses
  `lift_closed` and `inst_closed` included) and every hook. A closed term's value depends on
  the valuation only below `k`. `lift n k e e2` makes `e2` at `p ++ q ++ s` equal `e` at
  `p ++ s` (`p` of length `k`, `q` of length `n`). `inst k e a e2` makes `e2` at `p ++ s`
  equal `e` at `p ++ (x :: s)`, with `x` the value of `a` at `s`. For contexts: a variable's
  entry in a valuation satisfying the context is in the value of the type `lookup` gives it; a
  valuation of `G2` with `cext n G G2` is `q ++ t` with `q` of length `n` and `t` satisfying
  `G`; and with `cinst k G0 A0 a G1 G` and `a` of type `A0` in `G0`, a valuation of `G` is
  `p ++ t` with `t` satisfying `G0` and `p ++ (x :: t)` satisfying `G1`, `x` the value of `a`.
- **The remaining core rules** (`model-core.mm0`): `bvar_ty`, `app_df`, `beta`, `eta`, `inst_df`
  and `weak_df` are theorems for every hook too (`mbvar_ty` .. `mweak_df`), from the above and the
  function-space laws (`cpi_elim_ap`, `clam_ap`, `cpi_eta`). With the eight before, 14 of the
  15 core rules hold in the model for every hook. The fifteenth, `eeqv_df`, holds for every
  hook that is invariant under `eeqv` (`meeqv_df`; `minv M`: a constructor the hook interprets
  denotes the same as every tree it is `eeqv` to), since `eeqv` trees then denote the same
  (`lrel2_eeqv_dt`, by induction on the trees). The hook's definition will have to satisfy
  `minv`.
- **The inductive types** (`model-ind.mm0`, `model-rec.mm0`, 2026-11-11, layer C5): the values
  of `ind_ty`, `ind_ctor` and `ind_rec`, as parts of a hook, all definitions and theorems (no
  axiom). The hook `mcv H` is built from `H` by a course-of-values recursion, so `H` sees the
  values of a node's proper subtrees, not only of its children (`dt_mcv`); a curried trace is
  a set of points `nest a y`. A block's types are the least fixed point `ifam` of an operator
  that is monotone by construction (one step at every candidate below that is an element of
  the universe), so it is a fixed point whatever the data; a type that is a proposition at the
  level valuation is valued by its collapse inside the operator. `ind_ty` is a type's entry
  when that lies in the curried `Π` of the parameters and the type's type (`igate`, `ityv`),
  and otherwise the trivial family `itriv`, whose fiber at each valid argument valuation is
  the one point `scons ∅ ∅`: `ind_ty_ty` has only `tys_ok` as a premise, so the value must
  have its type whatever the constructors (2026-11-12; for legal data the gate holds, layer
  E2). Until 2026-11-14 the failure value was `∅`, which let typings in a context with a
  recursive field hold vacuously; a fiber `{∅}` would not do either, since the empty trace
  is in every universe and so bounds no domain.
  `ind_ctor` is the trace of the constructor's tuple `c :: fields` (`∅` for a proposition), and
  `ind_rec` the trace, over the parameters, motives, minors, indices and major, of the fold, the
  least relation that relates a constructor's tuple to its minor at the fields and inductive
  hypotheses (`dt_ind_ty`, `dt_ind_ctor`, `dt_ind_rec`). That the typing and reduction rules of
  the schema hold of these values (positivity, the universe bound, the recursor's type, iota)
  is layer E, still to come.
- **The rules at `Nat`** (`model-nat.mm0`, 2026-11-11, a pilot of layer E): for every hook
  `mcv H` whose `H` has the three parts above (`hind`), `ind_ty_ty`, `ind_ctor_ty`,
  `ind_rec_ty` and iota hold at Lean's `Nat` with `mdeq` for `deq` (`mnat_ty`,
  `mnat_zero_ty`, `mnat_succ_ty`, `mnat_rec_ty`, `mnat_iota_zero`, `mnat_iota_succ`; the iota
  rules with each argument typed in place of the spine typing `sty`), all theorems. Nat's value
  is the set of its tuples, an element of `U_1`; the family, the constructors' values and the
  fold are computed from the definitions above, not assumed. The rest file's axioms are
  unchanged: the general rules are layer E.
- **Telescopes and positivity** (`model-tel.mm0`, 2026-11-12, layers D6 and E1): what the
  schema's bookkeeping relations (`pis`, `lams`, `capp`, `spine`, `pargs`, `rehead`, `npis`,
  `sinst`, `pinst`, `qinst`) do to the denotation, a telescope read over an outer valuation `s`
  through the shifted table `dsh u M s` (`pis P b T` makes `T`'s value the curried `Π` of `P`
  over `s` and `b`); and positivity: a positive field type's value grows with the entries for
  the block's types, so for a block with `ind_wf` one step of the family is monotone at
  candidates of the universe (`iop0_mono`) and the operator is that step there (`iop_iop0`).
  Definitions and theorems only.
- **The family in the universe, and the gate** (`model-wf.mm0`, 2026-11-14, layer E2): for a block well formed over atoms that hold in the model (`iwf`),
  the family is an element of `u` and each type's value is its entry (`ind_wf_igate`), by a bound
  on the elements over each parameters' valuation (the least fixed point of a continuous operator,
  `lfp_universe`). When the gate fails the value is the trivial family `itriv` (model-ind), which
  has its type (`ityv_ipi`), so `ind_ty_ty` needs no legality. It relies on the two premises added
  to the spec's `cwf`/`ctors_wf` (§4).
- **The types' and the constructors' typings** (`model-ctor.mm0`, 2026-11-15, layers E3 and
  E4): the value of `ind_ty D i` is an element of the value of `Π P, F` (`ind_ty_ty_sem`, for
  `F` binders over a sort, which `tys_ok` requires since 2026-11-15 through `tys_ty`'s `isort`
  premise, §4; the theorem still takes it as a hypothesis), and for a well-formed block the value of `ind_ctor D i c` is an
  element of the value of `Π P, K2`, `K2` the constructor's type with the block's types put in
  (`ind_ctor_ty_wf`; without nested occurrences). The second reads the closedness of `Π P, K`
  off `ctors_wf` and uses the block's own valuation of its types as the instance.
- **Invariance under `eeqv`** (`model-inv.mm0`, 2026-11-15, layer D4, in part): a hook is
  invariant (`minv`, which `meeqv_df` assumes) when each node it interprets is, given that the
  node's proper subtrees are (`minv_intro`); and the hook of the inductive types is so at
  `ind_ty` and `ind_ctor` nodes: blocks related by `ind_eqv` have the same types' and
  constructors' values (`mcv_inv_ind_ty`, `mcv_inv_ind_ctor`; as the step of `minv_intro`:
  `mcv_inv_node_ind_ty`, `mcv_inv_node_ind_ctor`). The recursors' node is in `model-nst.mm0`
  (`mcv_inv_node_ind_rec`), the literals' in `model-lit.mm0`, the constants' in
  `model-top.mm0` (the quotient primitives are constants).
- **The rules of the schema, the quotients and the literals** (`model-fold.mm0`,
  `model-nst.mm0`, `model-quot.mm0`, `model-lit.mm0`, 2026-11-15 to 2026-11-20, layers E to
  G): every rule of Part III holds in the model for a hook with the parts concerned, at every
  block, nested or not. Definitions and theorems only. The division-like rules (§5) read each
  premise "a proof of `T` exists" as an element of the value of `T`, and two theorems turn
  such elements into arithmetic: the model's `Eq` is equality (`meqs_i`), and the model's
  `Nat.le` at two numerals is the truth value of `⊆` on their numbers (`mles_i`, over
  `le_D_wf`: the constructors give an element by induction, the recursor at the motive
  `nlev` gives the converse). So the functions of `divmod_eqs` are `ndiv` and `nmod` on the
  numerals, that of `gcd_eqs` is `ngcd` (strong induction), and a function with the
  recurrence of `land_eqs`, `lor_eqs` or `xor_eqs` computes `band`, `bor` or `bxor` on the
  binary numerals (strong induction on the first argument, with the cases at zero apart).
- **The assembly** (`model-top.mm0`, 2026-11-20). The hook is fixed: `hfin`, the union of the
  parts for the inductive types, their constructors and recursors, the literals and the
  constants. It is a function (the parts are, and their keys
  carry different labels) and invariant under `eeqv` (`hfin_minv`). The spec's `deq G e e2 A`
  is the definition `mdeq (mcv hfin) G e e2 A`: in every admissible universe, at every level
  valuation and every valuation satisfying `G`, the two sides have the same value, an element
  of the value of `A`. `inh` is `minh` at the same hook, and each relation of Part II over
  `⊢` is lean-tg3's `R_j` at the class `jmod (mcv hfin)` of the judgment atoms that hold in
  the model. With these definitions, all axioms of Parts II and III are theorems
  with the spec's statements: the 47 clauses are instances of lean-tg3's, and the rules are
  the model's theorems at `hfin`. As for `leqv`, replacing an axiomatized relation by a
  definition that satisfies its axioms is conservative for the certificate's proofs.
- **The opaque constants** (`model-top.mm0`). The value of `cst a S` is
  `Env ⟨ u , ⟨ a , values of S ⟩ ⟩` cut to the universe `u`, for a class `Env` declared as a
  term with no axiom (`hcst`, `dt_cst`). It depends on the levels only through their values,
  which is what `eeqv_cst` needs (`lrel2_lseqv_lsv`, `mcv_inv_node_cst`). The spec has no
  typing rule for `cst`: a certificate's typing axioms for its opaque constants, which are
  judgments and so now set-theoretic statements, are the constraints on `Env`. They are the
  certificate's hypotheses, as before (§8); a certificate without such axioms assumes nothing
  about `Env`. Since 2026-11-22 only Lean's axioms are such constants (an opaque constant is an
  abstract definition by its value), and the environment the hook reads is `Envx` (model-quot),
  `Env` without its entries at the spec's seven atoms and with the graphs of the values there:
  `∅`, the proof of a true proposition, at `propext_atom`, `quot_sound_atom` and `quot_ind_atom`
  (`envx_propext`, `envx_quot_sound`, `envx_quot_ind`), the choice function at `choice_atom`
  (`envx_choice`: `chv` at the level's value), and at `quot_atom`, `quot_mk_atom`,
  `quot_lift_atom` the traces of the quotients, the classes and the lifts over the types of the
  level's universe (`envx_quot`, `envx_quot_mk`, `envx_quot_lift`; since 2026-11-23, when the
  quotient primitives became constants: before, four parts of the hook at four expression
  constructors). The quotient rules read these values through `dt_cst` (`dt_quot*`), and
  `propext_ty`, `quot_sound_ty` and `choice_ty` likewise (§4; model-ci, from model-quot's
  `propext_inh`, `quot_sound_inh` and `choice_mem`).
- *Consistency* (2026-11-22). model-ci's `lean_consistent`: from `ty nil e (pi Prop (bvar nz))`, a
  contradiction in the set theory (an admissible universe exists, `uadm_exists`; the constant-zero
  valuation of the levels; the value of `Π (p : Prop), p` there is the empty product over the
  truth values). With the rules as theorems this is a relative consistency proof by
  interpretation, and it does not depend on what the definitions are: no reading of the model is
  needed to conclude that the spec's rules, the three standard axioms among them, derive no
  closed proof of `False` unless the set theory is inconsistent.

**TG mode: a certificate verified against the library** (2026-11-09). The same certificate
can be checked against the library instead of the spec:

- **The text.** `lean0 joined --tg STATEMENTS.mm0...` is the library, embedded in the trusted
  crate (`lean0-check/src/tg.rs`): `lean-tg-rest.mm0` with each `import` line replaced by the
  imported file, the first time only, as `abc join` does. Then come the earlier parts'
  statements, restated as in §7, and the certificate's own statements. `lean0 spec --tg`
  prints the library's text.
- **The file.** `lean0 tg-link CERT.mmb LIB.mmb OUT.mmb` writes the library's own MMB file
  (made by `abc`, with every library proof; `scripts/tg-check.sh` makes it) followed by the
  certificate's statements after the spec's, renumbered. The certificate's copies of the
  spec's statements are dropped. Each is first looked up by name in the library and checked
  to be the same statement: the same argument sorts and the same hypotheses and conclusion,
  or for a definition the same value. A term of the spec may be a definition in the library
  (Part I's relations), since the certificate's proofs never unfold a term of the spec. This
  tool is not trusted: the verifiers check the library's proofs and the certificate's
  together against the trusted text, so a wrong link fails.
- **New constants.** A certificate's terms are atoms and blocks (§8), which the encoding
  reads as leaves. The terms `lean0 joined` writes for an earlier part's abstract definitions
  (§7) are constants of sort `expr`, a sort that is not open. Read each one as the tree of the
  body its part gives it. That tree is in `ofsort lsig lopen ks_expr`, so the sorting axiom
  holds. No constructor equation mentions the constant, so §7's argument goes through
  unchanged.
- **Names.** The generator leaves the library's names alone: its terms, definitions,
  theorems and axioms, and the notation tokens that look like identifiers. So a
  certificate's statements read the same after the library as after the spec. A collision
  would only make the verifiers reject the file.

`scripts/test.sh` verifies every test module both ways (`scripts/certify.sh --tg`), and a
multi-part certificate in TG mode. It also checks that a tampered theorem is rejected in TG
mode, and that a tampered axiom of the spec cannot be linked.
