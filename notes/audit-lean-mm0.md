# Audit: `spec/lean.mm0` against Lean4Lean (@ 67f63b0)

Scope: every axiom in `spec/lean.mm0`. §1–3 audit the core rules (the judgment, the levels,
`lift`/`inst`/`closed` and the contexts; the spec's first 204 lines at the time); §4–8 argue
the additions since, §9 the notations, and §10 describes how the encoding departs from
Lean4Lean's presentation and the spec's division into three parts (syntax; definitions over
the judgment; the rules), with `lean0 modes` as the mechanical check that the first two parts
are definitions (§4, *Functionality*). Lean4Lean paths are relative to
`refs/lean4lean/Lean4Lean/` (`scripts/fetch-refs.sh`). The model-search scripts mentioned
below (`build/audit/`) are not part of the repository.

**Bottom line: no soundness problem found.** Every axiom holds in the intended model, and
every `deq` axiom of the core is a verbatim instance of an `IsDefEq` constructor; the
inductive schema (§4, stage B) is new trusted design argued in the thesis's model, with the
kernel's recursor types and rules compared on every block. The real gaps are about
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
  every axiom argument explicitly, and every sort is inhabited (`nz`, `lz`, `srt lz`, `nil`). So
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
| `sty_nil`, `sty_app` | D | `sty G h A e T`: `e` is `h` applied to `a1 … an`, `A` is a `Π` telescope over them as written (no conversion between the steps), `ai` has the type of the `i`-th binder at `a1 … a(i-1)`, and `T` is the rest. A computing relation (mode `+*++-`: `T` from the rest, the head given up to its constructor, `lean0 modes`). It is the premise of the reduction rules of recursors and quotients, which need every argument in the head's domain: a typing of the whole left side gives that only by inversion of its derivation (§4, 2026-11-04) |
| `bvar` (168) | T | :19 |
| `symm` (170) | T | :20 |
| `trans` (172) | T | :21, same type `A` on both premises |
| `sortDF` (174) | T, WF dropped | :22-24. The result type is `sort (succ l)` with the **left** `l`, as in Lean4Lean. Dropping WF is sound (§1) |
| `appDF` (176) | T | :32-35. The result is `B.inst a` with the **left** argument `a`. `inst nz B a R` is `R = inst B a 0` ✓ |
| `lamDF` (179) | T | :36-39. The body context is `A::Γ` with the **left** `A`, and the result is `forallE A B` (left `A`) ✓ |
| `forallEDF` (182) | T | :40-43. Body context `A::Γ` (left), result `sort (imax u v)` ✓ |
| `defeqDF` (185) | T | :44 |
| `beta` (187) | T | :45-47. Premises `A::Γ ⊢ e : B` and `Γ ⊢ a : A`. The result is `e.inst a : B.inst a`, both at `k=0` ✓ |
| `eta` (190) | T | :48-50. `e.lift = liftN 1 e 0` is `lift 1 0 e e1` ✓. The binder type `A` of the λ is the one in `forallE A B` ✓ |
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

## 4. Level case splits, the inductive schema and the generated per-declaration axioms (argued here, to be re-audited)

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

### The inductive schema (stage B, `spec/lean.mm0`, the inductive sections of Parts I–III; argued here, to be re-audited)

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

**Representation.** A block is `ind_mk b P T`: an atom `b` (a `term X_blk: blk` per block,
so that structurally equal declarations stay distinct), the parameters `P` as a `ctx`
(innermost first, each type under the earlier ones) and the types `T`, each with its type
`F = Π indices. srt l` (under `P`) and its constructors' types. A constructor type is
written under `P` and, outside `P`, under the block's `n` types as variables: at depth `d`
type `j` is `#(d + np + j)`. Binder type annotations (`outParam`, `optParam`, ...) are
consumed, as the kernel does before it builds recursors (`withLocalDecl ...
dom.consumeTypeAnnotations`), so the data states the declaration the kernel works with; the
exported types of the type formers and constructors (annotations kept) are reached by a
definitional cast, which the certificate proves (§8 says what the checker compares).
`ind_ty D i`, `ind_ctor D i c` and `ind_rec D i v` are the block's constants; `proj b i e`
the projections. A nested block is `ind_mkn b P T N` (below).

**Model.** Fix an assignment of the level variables and a valuation of `G`. A block whose
types are well formed (`tys_ok`) is interpreted by families of sets over the parameters and
indices: if the block is legal (`ind_wf`), the least fixed point of its constructors'
operator (the thesis's construction: positivity makes the operator monotone and the
universe conditions keep the fixed point in `srt l`), each element tagged by the data term
`D` and the constructor and field values, so that two blocks, or two instances of one block
at inequivalent levels, have disjoint values; `ind_ctor` is the tagging injection and
`ind_rec D i v` the unique fold (structural recursion), which exists for every motive
family in `srt v` whenever `elim_ok` holds (large elimination; or small elimination into
propositions, which is trivial under proof irrelevance). If the block is not legal, every
`ind_ty D i` is the empty family and `ind_ctor`, `ind_rec` arbitrary: they are then typed by
no axiom, since every typing axiom but `ind_ty_ty` has `ind_wf` as a premise. `proj b i e`
is the `i`th component of the tuple `e` when `e` is an element of a structure-like type of a
block with atom `b`, else arbitrary. `eeqv e e2` holds exactly when `e` and `e2` have the
same shape with equivalent levels, so they denote the same value.

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
| `ipos` (`checkPositivity`), `recfield` (`isRecArg`) | `ipos`: no occurrence, or `Π` over a domain without one (the kernel: an occurrence in a domain is non-positive), or a valid occurrence. `recfield`: a valid occurrence under `Π`s (a reflexive field). Both syntactic where the kernel uses `whnf` first; a block where that matters is left to stage A. |
| `ulevel` (`checkConstructors`' universe test) | `l ≈ 0` or `l ⊔ u ≈ l` are the semantic readings of `isAlwaysZero` and `geq'`, which are sound approximations of them: whatever the kernel accepts, these accept, and both conditions are what the fixed point in `srt l` needs (a type in `Prop` may have fields of any size; otherwise each field's universe is at most the type's). |
| `cwf`, `ctors_wf` | Each field's type (with the block's types put in) is a type in the context of the parameters and the earlier fields (`⟨ Ctx ⊢ A2 : srt u ⟩`), of an allowed level, positive; the result is the constructor's own type applied to the parameters and to indices without occurrences. This is `checkConstructors`, with the parameters matched syntactically (the data has one telescope `P`) where the kernel uses `isDefEq`; the generator checks that before it states the data, else stage A. |
| `tys_ty`, `tys_ok`, `ctx_wf`, `tys_wf`, `ind_wf` | `checkInductiveTypes`: the parameters are types over the earlier ones, each type's type is a type of the form `Π indices. srt l2` with `l2 ≈ l`, the block's universe being the first type's (the kernel: `isEquiv`). `tys_ok` alone types the type formers (the kernel adds them before it checks the constructors; in the model an illegal block's types are empty families, so typing the formers needs no legality). |
| `elim_ok`, `large`, `fir`, `leaf_has` (`isLargeEliminator`) | `v ≈ 0` always (small elimination). Large elimination when `ls lz ⊔ l ≈ l` (never a proposition, `isNeverZero`), or one type with no constructors (empty: the fold is vacuous), or one type with one constructor each of whose fields is a proposition (`⟨ Ctx ⊢ A2 : srt lz ⟩`, where the kernel tests `isAlwaysZero` syntactically) or occurs as an argument of the constructor's result (`has_arg`, a syntactic occurrence as a whole argument, as the kernel's `contains`): subsingleton elimination, since such a type has at most one element per index under proof irrelevance, so the fold into any universe is determined. |
| `mty`, `motives` (`mkRecInfos`' motives) | Motive `j` is `Π indices. Π (ind_ty D j params indices). srt v`, read off `F_j` lifted over the `j` earlier motives: at depth `d` inside it the parameters are `#(d+j+np-1) .. #(d+j)` and the indices `#(d-1) .. #0`. The context lists motive `n-1` first (innermost): `capp Mr (Mj :: [])` appends the outer one. |
| `ihty`, `mwalk`, `cminors`, `minors` (minor premises) | Minor `k` for constructor `c` of type `i` is `Π fields. Π ihs. motive_i indices (ind_ctor D i c params fields)`. `mwalk` walks the constructor type at depth `d` with `r` recursive fields passed: a field type is lifted by `k + n` at depth `d` (over the `k` earlier minors and `n` motives, which sit between the parameters and the fields); a recursive field's hypothesis is its type lifted by `r + nf - d` (over the hypotheses before it and the fields after it), with the head `ind_ty D j params` replaced by motive `j` at `#(y + r + nf + k + n - 1 - j)` under `y` binders of its own telescope, applied to the field `#(y + r + nf - 1 - d)` and those binders. The hypotheses are collected innermost first (`IH :: Ihs`). At the leaf (`d = nf`, which `mwalk_res` requires by using one variable for both) the result is lifted by `k + n` at depth `nf` and by `r` at depth 0, its head `#h` (the type variable, so lifted) applied to `np` arguments is replaced by motive `i` at `#(r + nf + k + n - 1 - i)`, and the constructor is applied to the parameters `#(r+nf+k+n+np-1) ..` and the fields `#(r+nf-1) .. #r`. `cminors`/`minors` append each next minor outside the later ones. |
| `rtail`, `rec_ty` | `Π P. Π M. Π N. Π indices. Π major. motive_i indices major`, with `F_i` lifted over the `m + n` motives and minors; under the indices (depth `d`) and the major, motive `i` is `#(d + m + n - i)` and the indices `#d .. #1`. This is the kernel's `ty` in `AddInductive.run`. |
| `ihval`, `rwalk`, `rec_rhs` (`mkRecRules`) | `λ P. λ M. λ N. λ fields. minor_k fields ihs`, the minor at `#(nf + m - 1 - k)` under the fields; each recursive field's hypothesis is `λ ys. ind_rec D j v params motives minors indices (field ys)`, with the recursor's arguments the variables above the fields: parameters at `#(y+nf+m+n+np-1) ..`, motives and minors `#(y+nf+m+n-1) .. #(y+nf)`, the field at `#(y + nf - 1 - d)`. |
| `ind_ty_ty`, `ind_ctor_ty` | The type former has type `Π P. F_i` under `tys_ok`; constructor `c` of type `i` has type `Π P. K` with the block's types put in, under `ind_wf`: in the model, the families and the tagging injections have these types. |
| `ind_rec_ty` | Under `ind_wf` and `elim_ok`, the fold has the type `rec_ty` computes (the thesis's recursor; the argument that `rec_ty` computes the kernel's type is the two rows above, tested on every block). |
| `ind_iota` | `ind_rec D i v ps ms ns is (ind_ctor D2 i c qs fs) ≡ R ps ms ns fs` where `R` is `rec_rhs`'s term: the fold's computation rule. The constructor's block `D2`, its parameters `qs` and the indices `is` are free (as in nanoda's `reduce_rec`, which compares none of them); the premise `sty G (ind_rec D i v) RT (e4 @ maj) T`, with `RT` the recursor's type (`rec_ty` then `rst`, as in `ind_rec_ty`), types every argument at its binder's type, so the major's type is `ind_ty D i ps is`, and by the tagging in the model this forces `D2` to be `D` at equivalent levels and the arguments to agree. The premise states that every argument is in the recursor's domain, which the fold's computation rule needs; until 2026-11-04 the rule took a typing of the whole left side, which says that only through inversion of its derivation. The application spine is taken apart by `spine` and `rehead`, which fix `D`, `i`, `v`, `c` and the counts before the derived terms are matched. |
| `struct_like`, `field_ty`, `proj_ok`, `fprops`, `pinst`, `qinst`, `proj_ty` | Typing of `proj b i e` for `e : ind_ty D j ps`, type `j` structure-like (one constructor, no indices; the kernel's `is_structure_like`, which a type of a mutual block may satisfy): the field's type with the parameters and then the earlier projections put in, outermost first (`pinst` recurses to the innermost argument of `S` and substitutes on the way out; `qinst` fields `0 ..` at `#(k-1) ..`), a simultaneous substitution since each term substituted is lifted over the binders below it. `proj_ok`: the type's sort is at least 1, or the fields up to `i` are propositions (`fprops`: each `⟨ Ctx ⊢ A2 : srt lz ⟩`) — the argument of stage A's `_dfp`: such projections are definable by elimination into `Prop`, and nanoda requires less (only the dependent fields), so this is no more permissive. |
| `proj_mk` | `proj b i (ind_ctor D2 j nz qs fs) ≡ fs[i]` when well typed (`spine (Y @ f) M ii` with `ii = nf - 1 - i`: the field counted from the outside); the constructor's block is free as in `ind_iota`. |
| `nonrec`, `eta_ok`, `projs`, `ind_eta` | Eta for a structure-like type none of whose fields mentions the block (`closed (d + np)` for each domain): `e ≡ ind_ctor D j nz ps (proj b 0 e) ... (proj b (nf-1) e)` at `e`'s type, since such a type is a product in the model. (The kernel requires the block not to be recursive at all; this accepts a non-recursive type of a recursive mutual block too, which is still a product.) |
| `ind_mkn`, `ind_data_n`, `ind_nested`, `ndecl`, `cnth`, `aux_of`, `rst`, `spz`, `nst_hit`, `spz_ctors`, `aux_data`, `nst_ok`, `nst_group`, `rec_rule`, `ind_iota_nst`, `pinst_head_c` (nested blocks, B2; `ElimNestedInductive`) | A nested block `ind_mkn b P T N` is the mutual block the kernel checks in its place: `T` lists the declared types and then one auxiliary type per nested occurrence `I Ds` of an earlier block `I` (in the kernel's order), and `N` the occurrences, each `ind_ty I i @ Ds` written like a constructor type at depth 0 (`Ds` mention the block's types; the kernel requires them to mention no bound variable, and a parameter `Ds` that mentions none makes no occurrence, so the certificate's `N` must be the kernel's list, which the checker's comparison of the recursor types enforces, §8). Every relation of the schema (`ind_wf`, `elim_ok`, `rec_ty`, `rec_rhs`, `struct_like`, `eta_ok`, ...) reads the mutual data, as the kernel runs `AddInductive` on the specialized block; three additions make it the kernel's nested block. (1) `nst_ok` (a premise of `ind_wf`): the occurrences come in groups, one per declared type of a well-formed block `I` in order with the same arguments (`I.all`, which excludes `I`'s own auxiliary types), and each auxiliary type's data is `I`'s type's type at `Ds` (`pinst`) and `I`'s constructors specialized (`spz_ctors`: `I`'s types put in by `sinst`, `I`'s own occurrences restored by `rst` since `I` may be nested, the parameters replaced by `Ds` by `pinst`, then `spz`, which replaces each occurrence `I' Ds' is` of `N` at depth `d` by `#(d + np + j)` applied to the block's parameters and to `is`, from the outside in as `replaceAllNested` does; the lookup `nst_hit` tries the entries by clause alternatives, since the prover does not re-enter a finished premise). So the auxiliary types are exactly the kernel's `_nested.X_k`, and `tys_wf` on the mutual data is the kernel's positivity and universe check on them. (2) `rst D N e e2` (`restoreNested`): `ind_ty D j ps is` for an auxiliary type `j` is read as `I Ds[ps] is` (`sinst` then `pinst`, the parameters applied being the ones substituted) and `ind_ctor D j c ps fs` as `ind_ctor I i c Ds[ps] fs`; nothing else changes, and the identity when `N = []` (`rst_nil`; `rst_refl` is the last clause so that an unknown result is computed by the traversal). `ind_ctor_ty`, `ind_rec_ty`, `proj_ty` (the field's type, before the parameters and projections are put in, so that the substitution hypotheses of the structure lemmas match) and `rec_rule` (the rule's right-hand side, used by both iota axioms) restore what they state. (3) `ind_iota_nst`: the recursor of an auxiliary type `i` (the block's `X.rec_k`, `mkAuxRecNameMap`) reduces on `I`'s constructor `c`, `ind_rec D i v ps ms ns is (ind_ctor I2 ii c qs fs) ≡ R ps ms ns fs`, the fields being the last `nf` arguments of the major premise as in `inductive_reduce_rec` (whose comment notes that the constructor's parameters need not be the recursor's). *Model.* The auxiliary type `j` of a legal nested block is interpreted as the family `I Ds` itself: by (1) its constructors are `I`'s at `Ds` with the occurrences written as the block's own types, so the mutual fixed point's component `j` and the family `I Ds` (the fixed point of `I`'s operator at the parameters `Ds`, which the mutual fixed point already contains) satisfy the same equations, and the least fixed point is unique; this is the kernel's justification for restoring. Under that reading `rst` is the identity on values, so the restored typings are the mutual block's, and `ind_iota_nst` is the mutual block's iota for the constructor `ind_ctor D i c`, whose value is `ind_ctor I ii c Ds[ps]`'s; the `sty` premise (from the recursor's restored type, as in `ind_iota`) makes `I2` an instance of `I` at equivalent levels and `qs` the occurrence's arguments at `ps`. `ind_eqv` compares `N` as well as `P` and `T`, since two blocks with the same atom and mutual data but different occurrences denote different families. The elimination level and `is_rec` (no eta for a structure with a nested field) are the mutual block's, as in the kernel. |
| `eeqv_*`, `ind_eqv`, `ceqv`, `teqv`, `cseqv`, `lseqv`, `eeqv_df` | `eeqv` is the structural congruence with `leqv` at sorts and recursor levels, `ind_eqv` (same atom, componentwise `eeqv`) at the block constants, and `lseqv` (entrywise `leqv`) at an opaque constant's levels (`eeqv_cst`: the same atom; the atom's interpretation is a function of the levels' values). `eeqv_df`: expressions of the same shape at equivalent levels denote the same value, so they are defeq at any type of one of them (this generalizes `sortDF` and `constDF`). A generated term that is not a public definition (an opaque, an axiom, a theorem, a stage-A constant) has no `eeqv` clause, so a block whose data mentions one at its levels gets `axiom c_eeqv (us us2): leqv u u2 > ... > eeqv (c us) (c us2)`, once per constant (`induct::eeqv_axioms`; the generator's report counts them): the same constant at equivalent levels, which is what `eeqv` means. `lean0 check` checks its shape (§8). A `_df` lemma whose `eeqv` still fails is stated as an axiom and counted. |
| `nat_D`, `eq_D`; `closed_quot*`, `eeqv_quot*`, `quot_ty`, `quot_mk_ty`, `quot_lift_ty`, `quot_ind_ty`, `quot_lift_mk`, `quot_ind_mk` | Lean's prelude blocks `Nat` and `Eq` are stated as spec data (between the spec's `lean0-check` marks, in prefix form), so that the quotient primitives' types (which mention `Eq`) and the literal ties (§5) can be spec axioms. The generator uses them only when the export's block is exactly this data (else the block is generated as usual, and the quotient primitives fall back to the stage-A axioms); `lean0 check` compares the export's `Nat` and `Eq` with them like any block (§8). The quotient primitives are constants with the types the kernel requires when it adds them (`quot.cpp`, `check_quot_decls`: `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` have exactly these types, with `Eq` checked to be the expected inductive), level invariance and closedness as for any constant, and the reduction rules `Quot.lift f h (Quot.mk r a) ≡ f a` and `Quot.ind h (Quot.mk r a) ≡ h a` when every argument has its binder's type in the primitive's type (`sty`; Lean4Lean's quotient `extra` rules; nanoda's `reduce_quot` checks only the spine, and the typing makes the constructor's `α` and `r` the primitive's, `Quot` being injective as a type former in the model). Sound in the model: the quotient of a type by a relation, with `Quot.lift` well defined by its hypothesis and `Quot.ind` by induction on representatives. |

**What `ind_wf` does not say.** Duplicate constructor names, `checkNoMVarNoFVar`, the
`_nested` prefix: naming matters, not typing. The syntactic places where the kernel uses
`whnf` (`isRecArg`, `checkPositivity`, the parameter match) make a block fall back to stage
A, counted and reported by `lean0 gen`.

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
field `V (V α)` (`ipos`, through `indapp` and `iargs`). nanoda rejects all six as well (two by
not terminating, `historical/upstream-issues.md`).

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
restoration, sound since an auxiliary type denotes its occurrence (below). Totals: 113
relations with 162 computing clauses, 110 checking clauses and the 8 clauses of `rst`, and 74
rules. `scripts/test.sh` runs the check and requires a spec with an overlapping clause to be
rejected.

### Generated per-declaration axioms (stage A, `lean0/src/gen.rs`)

These live in the generated `.mm0`, not in `lean.mm0`, and must be read against the Lean
declaration. They remain for the blocks the schema does not cover (the `whnf` places above), and for a
quotient primitive whose type is not the spec's (above). They are trusted in the same sense that
nanoda trusts the export's recursors (which it re-derives and compares): nothing trusted
checks that such a declaration is legal or that its recursor is the one the declaration
determines, so the arguments below hold per kind of axiom, *assuming* the declaration is
legal and the export's recursor is the right one.

| axiom class | Lean4Lean counterpart / argument |
|---|---|
| `c_df` (axioms, stage-A inductive types, constructors, recursors, opaques) | `constDF` for a constant whose type is the given `T` (`T` is checked well-typed by the public theorem `c_wf`) |
| `c_atom` (term of sort `atom`) and `c` (def, `cst c_atom (lcons u1 ... lnil)`) | the constant itself: an atom of its own at its levels (§10). `c_closed` is a theorem (`closed_cst`) and the level congruence is the spec's `eeqv_cst`, so neither is an axiom (until 2026-11-04 both were generated axioms, 260 and 24 of them in Init) |
| `c_eeqv`: `leqv u u2 > ... > eeqv (c us) (c us2)` (only for a constant, now a theorem of an earlier part or a constant of a stage-A block, that an inductive declaration mentions at its levels; above) | the same constant at equivalent levels has the same shape (`eeqv` is defined that way) |
| `R_c` (def) + `R_c_iota`: `sty G rec RT LHS T > deq G LHS (R_c ps ms mins fs) T` | The iota rule of the exported recursor rule: `rec ps ms mins is (c cps fs) ≡ val ps ms mins fs` whenever every argument has its binder's type in the recursor's exported type `RT` (`sty`). The constructor's parameters, levels and the indices are separate variables, as in nanoda's `reduce_rec`. They are forced to agree with the recursor's by the premise (it makes the major's type `I ps is`, and inductive type formers are injective in the model). |
| `S_proj_i_df` | Typing of `proj b i e` (the spec's `proj`, with the block's atom `b`) for `e : S us ps`: the field type with parameters and earlier projections substituted (the `inst` premises do this outermost-first, which is simultaneous substitution). The premise `leqv (lmax (ls lz) L) L` (sort at least 1) is present unless every field up to `i` is a proposition, matching nanoda's `infer_proj` restriction for structures that may be propositions. |
| `S_proj_i_dfp` | The same typing, for projecting from a structure that is a proposition: premises `leqv L_j lz` for every field `j ≤ i` that is not a proposition at all levels (`L_j` the level of field `j`'s sort). Generated only when each such `L_j` can be zero. Sound: with every field up to `i` a proposition, `e.0, …, e.i` are definable by eliminating `e` into `Prop`, which is allowed for every inductive proposition, and the field types agree by proof irrelevance. nanoda's `infer_proj` (like Lean's kernel) requires only the fields that the projected one depends on to be propositions; requiring all of them up to `i` is stronger, so this is no more permissive. |
| `S_proj_i_mk` | `(S.mk ps fs).i ≡ fs[i]` when well-typed (nanoda's `reduce_proj`). |
| `S_eta` | Structure eta for non-recursive structures (one constructor, no indices): `e ≡ S.mk ps (e.0) … (e.n)` at `S us ps`. Unit eta and nanoda's iota-on-structure expansion are derived from it. |
| `Quot_lift_mk`, `Quot_ind_mk` (only for a quotient primitive whose type is not the spec's) | `Quot.lift f h (Quot.mk r a) ≡ f a` and `Quot.ind f (Quot.mk r a) ≡ f a` when every argument has its binder's type in the primitive's exported type (`sty`; Lean4Lean's quotient `extra` rules; the spec's `quot_lift_mk`/`quot_ind_mk` above). |

K-like reduction (`Eq.rec` on a non-constructor) has no axiom: the major premise is replaced by
the constructor using `proofIrrel`.

## 5. Nat literals (argued here, to be re-audited)

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
| generated (stage A, only when the operation's equations below could not be derived; the run reports it): `Nat_add_lit`, `Nat_sub_lit`/`_lit0`, `Nat_mul_lit`, `Nat_beq_lit`/`_lit_lt`/`_lit_gt`, `Nat_ble_lit`/`_lit_gt`, `Nat_pow_lit`, `Nat_shiftLeft_lit`, `Nat_shiftRight_lit`, `Nat_div_lit`/`_lit0`, `Nat_mod_lit`/`_lit0`, `Nat_gcd_lit`/`_lit2`, `Nat_land_lit`, `Nat_lor_lit`, `Nat_xor_lit` | `op (succ^a zero) (succ^b zero) ≡ succ^(f a b) zero : Nat` (or `≡ Bool.true/false : Bool`), where the premises force the value: `sub` from `c+b = a` or `a+c = b`; `div`/`mod` from `q·b = m`, `m+r = a`, `r+x+1 = b` (so `r < b`, Euclidean division, and `b = 0` has its own axiom: `a/0 = 0`, `a%0 = a`); `gcd` from `g·p = a`, `g·q = b` (`g` divides both) and `x·a = y·b + g` or `y·b = x·a + g` (every common divisor divides `g`, so `g = gcd a b`; `a = b = 0` forces `g = 0`); `beq` false from `a+c+1 = b` or `b+c+1 = a`; `ble` from `a+c = b` / `b+c+1 = a`; shifts via `2^b`. |

**Trust gap of the generated operation axioms (stage A).** They are valid only if the
environment's definition of the operation computes it on numerals, which is Lean4Lean's
`HasPrimitives` invariant. Lean4Lean establishes it by checking defining equations when the
definition is added (`Primitive.lean`: e.g. `Nat.add x 0 ≡ x` and
`Nat.add x (succ y) ≡ succ (Nat.add x y)` for fresh `x y`; well-founded unfolding through
`WellFounded.Nat.fix`, `dite` and `Decidable` reflection for `gcd`, `div`, `mod` and the
bitwise operations). A generated axiom, like nanoda and the C++ kernel, only checks the name
and the type (`Nat → Nat → Nat`, or `→ Bool` for `beq`/`ble`). Every operation has rules in
the spec (stage B, below), so a certificate falls back to the axiom only when the derivation
of the equations failed, which the run reports.

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
environment. `Nat.div`, `Nat.mod`, `Nat.gcd` and the bitwise operations, whose equations go
through fuel or well-founded recursion, `dite` and `Decidable` reflection, are the next
subsection.

Conventions of the arguments: `n̄` is `lit n`, `N`, `Z` and `S` are `nat_ty`, `nat_zero` and
`nat_succ`; `Γ ⊢ n̄ : N` for every `n` by `lit_zero`/`lit_succ` (the typing of a `deq`); an
equation over fresh variables is instantiated at literals by substitution (`IsDefEq.instN`,
the spec's `instDF`; the equations are stated in extended contexts, so `f` must be closed
for the premises' `f` to be the lifting of the conclusion's `f`, which is why every
function the equations mention is required closed, directly or by its own relation);
`f ā ≡ f ā : Π N. N` from the typing premise and `ā : N`, so the congruence `appDF` turns
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

### The division-like operations (`spec/lean.mm0`, "The division-like operations"; `lean0/src/natrec.rs`)

Lean4Lean's checks of `Nat.div`, `Nat.mod` (`checkNatFuelRec`), `Nat.gcd` (`checkNatGcd`)
and `Nat.bitwise` with `land`/`lor`/`xor` (`checkNatBitwise`, `checkNatLAnd`, ...) go through
`dite`/`ite` on decided propositions, the fuel recursions `Nat.div.go`/`Nat.modCore.go` and the
well-founded fixpoint `WellFounded.Nat.fix` (fuel recursion again, with the measure as fuel).
The spec states these checks as relations over variables standing for Lean's `@dite Nat`,
`@ite Nat`, `Not`, `Decidable`, `Decidable.intro` (`R`), `Bool.Reflects` (`T`), `Nat.decLe`,
`Nat.decEq`, the lemmas the recursive calls apply, and so on: nothing is assumed of them
beyond the stated equations, all variables under binders are required closed, and every
relation is introduced by its single `_i` rule, so only the `nat_*_lit` rules need an
argument. The generator (`natrec.rs`) builds the terms by name (the reflection is the new
`Decidable` structure: `T p b` is `Bool.Reflects b p`, `R` is `Decidable.intro`, `ofT`/`ofF` are
`λ p H. H`, the proofs `pf x y` are `Decidable.reflects_decide`), reads the fixpoint's parts
(`al`, `motive`, `hm`, `F`, the packing `pack`, the recursive call's lemma `pfF`/`pfB`) off the
`_unary` definitions, derives each premise with nanoda (`Elab::defeq` over fresh locals) and
states `Nat_div_eqs` etc.; the `_lit` theorems keep their stage-A statements.

Conventions, in addition to the previous subsection's: an equation whose context has
hypotheses of propositional types (`hy : leN 1̄ ȳ`, `H : Not (eqN (S m̄) 0̄)`, `ih : Π y. ltN (hm y)
(hm (pack ā b̄)) → motive y`) is instantiated at closed terms taken from the right-hand side of
an earlier equation, whose types are premises of the relations (2026-11-04: `ofT`, `ofF` in
`dec_eqs`; `leN`, `pf` and `eqN`, `pq` in `natle_dec`, `nateq_dec`; `go`, `pfs`, `lem` in
`div_eqs`, `mod_eqs`; `ltN`, `go al motive hm`, `pfx`, `pfgo` in `fix_eqs`; the functional,
`pack` and the call's lemma in `gcd_eqs`, `bitwise_eqs`; `bf` in `bitop_eqs`), so an
instance's arguments are in the binders' types without inversion of any derivation (the
generator derives each from the constant's Lean type by a cast). In particular the
recursive call `λ y hy. go … t y (pfgo …)` is in the motive's `Π` type at every fuel,
including `0`, by the typings of `go` and `pfgo`. By proof irrelevance which proof it is
does not matter; `appDF` with
`defeqDF` lets an argument's type be converted along a defeq (e.g. `pfx x : ltN (hm x) (eager
(S (hm x)))` where `ltN (hm x) (S ā)` is needed). **The decision lemma:** for literals `a b`,
`natle_dec`'s equation at `x := ā, y := b̄` gives `dleN ā b̄ ≡ R (leN ā b̄) (ble ā b̄) (pf ā b̄)`,
and `ble ā b̄ ≡ t` if `a ≤ b` (`nat_ble_lit`) or `≡ u` (`nat_ble_lit_gt`), so by congruence
(`pf ā b̄ : T (leN ā b̄) t` by conversion) and `dec_eqs`'s equation at `p := leN ā b̄`,
`H := pf ā b̄`: `dite (leN ā b̄) (dleN ā b̄) f g ≡ f (ofT ..)` when `a ≤ b` and `≡ g (ofF ..)`
otherwise, and by `ite_eqs` `ite (leN ā b̄) (dleN ā b̄) x y ≡ x` or `y`. The same with
`nateq_dec`, `beq` and `nat_beq_lit`/`_lt`/`_gt`: `dite (eqN ā b̄) (deqN ā b̄) f g` reduces to
the first branch iff `a = b`. **The Bool lemma:** by `bool_dec`, `dite (bp X) (bd X) (λ _. x)
(λ _. y) ≡ x` when `X ≡ t` and `≡ y` when `X ≡ u` (congruence, then the equation at
`a := x, b := y`), and likewise `ite`. **The fuel lemma** (`fix_eqs`): `go al motive hm F
(S k̄) x H ≡ F x (λ y hy. go al motive hm F k̄ y (pfgo k̄ x H y hy))` is the third equation at
`F, t := k̄, x, h := H`; `eager (S ā) ≡ ite (bp (beq (S ā) (S ā))) (bd ..) (S ā) (S ā) ≡ S ā`
by the second equation, `lit_succ`, `nat_beq_lit` and the Bool lemma; so `fix al motive hm
F x ≡ go al motive hm F (S ā) x (pfx x)` when `hm x ≡ ā` (the first equation, congruence).

| rule | argument |
|---|---|
| `nat_div_lit`: `div_eqs G .. f go pfs lem > bmul q b m > badd m r a > baddc r x b > f ā b̄ ≡ q̄` | `b ≥ 1`. Lemma: for all `k`, all `a' < k` and any proofs `H : leN 1̄ b̄`, `H'`: `go b̄ H k̄ ā' H' ≡ (a' div b)‾`, by induction on `k = k'+1` (`k̄ ≡ S k̄'`): the `go` equation at `x := ā', y := b̄, hy := H, fuel := k̄', h := H'` gives `dite (leN b̄ ā') (dleN b̄ ā') (λ h2. S (go b̄ H k̄' (sub ā' b̄) (lem ..))) (λ _. 0̄)`; if `b ≤ a'`, the decision lemma, `nat_sub_lit` (`sub ā' b̄ ≡ (a'-b)‾`), the hypothesis (`a'-b < k'` as `a' ≤ k'` and `b ≥ 1`) and `lit_succ` give `((a'-b) div b + 1)‾ = (a' div b)‾`; otherwise `0̄`. Then the top equation at `x := ā, y := b̄`, the decision lemma (`1 ≤ b`), beta, `S ā ≡ (a+1)‾` and the lemma at `k = a+1` give `(a div b)‾`, and the premises make `q = a div b`. |
| `nat_div_lit0`: `> f ā 0̄ ≡ 0̄` | the top equation at `y := 0̄`: `ble 1̄ 0̄ ≡ u` (`nat_ble_lit_gt`), so the second branch, `0̄`. |
| `nat_mod_lit`: `mod_eqs .. > (the same premises) > f ā b̄ ≡ r̄`; `nat_mod_lit0`: `> f ā 0̄ ≡ ā` | the lemma as for `div` with `go b̄ H k̄ ā' H' ≡ (a' mod b)‾` (`(a'-b) mod b = a' mod b` when `b ≤ a'`; the second branch is `x`, so `a'` when `b > a'`). `a = 0`: the base equation, `f 0̄ b̄ ≡ 0̄`, and the premises force `r = 0`. `a = a'+1`: the top equation at `x := ā', y := b̄` is `ite (leN b̄ (S ā')) (dleN ..) (dite (leN 1̄ b̄) (dleN ..) (λ hy. go b̄ hy (S (S ā')) (S ā') (pfs ..)) (λ _. S ā')) (S ā')`; if `b ≤ a` the `ite` takes the `dite`, which (`1 ≤ b`) is `go .. (S (S ā')) (S ā') _ ≡ (a mod b)‾` by the lemma; if `b > a` it is `S ā' ≡ ā = (a mod b)‾`. For `b = 0`: `a = 0` by the base equation; `a = a'+1`: `ble 0̄ ā ≡ t` takes the `dite`, and `ble 1̄ 0̄ ≡ u` its second branch, `S ā' ≡ ā`. |
| `nat_gcd_lit`: `gcd_eqs .. f pack F pfF > bmul g p a > bmul g q b > bmul x a m > bmul y b n > badd n g m > f ā b̄ ≡ ḡ`; `nat_gcd_lit2` with `badd m g n` | Lemma: for all `k`, all `a < k`, all `b` and any proof `H`: `go al motive hm F k̄ (pack ā b̄) H ≡ (gcd a b)‾`, by induction on `k = k'+1`: the fuel lemma gives `F (pack ā b̄) ih` with `ih = λ y hy. go .. k̄' y (pfgo ..)`, whose binder type is the probes' (`ltN (hm y) (hm (pack ā b̄))`). `a = 0`: the first probe at `n := b̄, ih` gives `b̄`. `a = a'+1` (`ā ≡ S ā'`): `beq (S ā') 0̄ ≡ u` (`nat_beq_lit_gt`), so `ofF (eqN (S ā') 0̄) (pq (S ā') 0̄) : Not (eqN (S ā') 0̄)` by conversion, and the second probe at `m := ā', n := b̄, H := that, ih` gives `ih (pack (fm b̄ (S ā')) (S ā')) (pfF ..)`, by beta `go .. k̄' (pack (fm b̄ ā) ā) _`, by `nat_mod_lit` and congruence `go .. k̄' (pack (b mod a)‾ ā) _`, by the hypothesis (`b mod a < a ≤ k'`) `(gcd (b mod a) a)‾ = (gcd a b)‾`. Then `f ā b̄ ≡ fix .. F (pack ā b̄)` (the top equation), `≡ go .. F (eager (S (hm (pack ā b̄)))) (pack ā b̄) (pfx ..)`, `≡ go .. (S ā) ..` (the measure equation `hm (pack ā b̄) ≡ ā`, the fuel lemma's `eager`), `≡ (gcd a b)‾` (the lemma at `k = a+1`). The premises make `g = gcd a b` as for the stage-A axiom (`g` divides both; `x·a = y·b + g` or `y·b = x·a + g` makes every common divisor divide `g`; `a = b = 0` forces `g = 0`). |
| `nat_land_lit`: `bitop_eqs .. f bf t u u u > band a b c > f ā b̄ ≡ c̄`; `nat_lor_lit` with `t t t u` and `bor`; `nat_xor_lit` with `u t t u` and `bxor` | Let `φ` be the function the probe's right-hand side computes: `φ 0 b = b` if `bf u t ≡ t` else `0`; `φ a 0 = a` if `bf t u ≡ t` else `0`; otherwise `φ a b = 2·φ (a div 2) (b div 2) + [bf (a mod 2 = 1) (b mod 2 = 1) ≡ t]`. Lemma: for all `k`, all `a < k`, all `b`, any `H`: `go al motive hm (Fb bf) k̄ (pack ā b̄) H ≡ (φ a b)‾`, by induction on `k` as for `gcd`: the fuel lemma, the probe at `bf, n := ā, m := b̄, ih` (`bf : Π B. Π B. B` by inversion from `f ≡ fb bf` and `fb`'s type), then the right-hand side: `dite (eqN ā 0̄) (deqN ā 0̄) ..` by the decision lemma (`nat_beq_lit`/`_gt`); in the `a = 0` branch `dite (bp (bf u t)) (bd (bf u t)) (λ _. b̄) (λ _. 0̄)` with `bf u t ≡ r3` (the truth table) and the Bool lemma; `b = 0` likewise with `r2`; otherwise `dec (eqN (fm ā 2̄) 1̄) (deqN (fm ā 2̄) 1̄) ≡ t` or `u` by `nat_mod_lit`, `nateq_dec`'s equation, `nat_beq_lit`/`_lt`/`_gt`, and the `dec` equation at `p := eqN .., b := t/u, H := pq ..` (the low bits), so `bf b1 b2 ≡ r_i` by the truth table, the Bool lemma picks `fa (fa r r) 1̄` or `fa r r` with `r = ih (pack (fd ā 2̄) (fd b̄ 2̄)) (pfB ā b̄ _)`, `≡ go .. k̄' (pack (a div 2)‾ (b div 2)‾) _` by beta, `nat_div_lit` and congruence, `≡ (φ (a div 2) (b div 2))‾` by the hypothesis (`a div 2 < a ≤ k'` as `a ≥ 1`), and `nat_add_lit` twice gives `(φ a b)‾`. Then `f ā b̄ ≡ fb bf ā b̄ ≡ fix .. (Fb bf) (pack ā b̄)` (the `bitop` and top equations), and as for `gcd` (measure, `eager`, the lemma at `k = a+1`) `≡ (φ a b)‾`. For the table `t u u u` (`and`), `φ` is bitwise and (`φ 0 b = 0`, `φ a 0 = 0`, bit by bit `a ∧ b`), which `band` computes; for `t t t u` (`or`) bitwise or (`φ 0 b = b`, `φ a 0 = a`); for `u t t u` (`xor`) bitwise xor. |

Nothing is assumed of `Not`, `Dec`, `T`, `R`, `ofT`, `ofF`, `al`, `motive`, `ltN` and the proof
terms beyond their occurrences in the equations; `Not`, `Dec` and `T` only type the
contexts' hypotheses, and every instantiation above is at a term whose type the previous
equations give.

String literals have no axioms: a string literal is translated as its expansion
`String.ofList [Char.ofNat n, …]` (Lean4Lean's translation; nanoda expands it in `def_eq`), so
every step about one is an ordinary derivation.

## 6. Substitution and weakening (argued here, to be re-audited)

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

### `cext` (`spec/lean.mm0`, "Contexts")

| MM0 | interpreted as |
|---|---|
| `cext n G G2` | `Ctx.LiftN n 0 G G2` (Typing/Lemmas.lean:8-10) |

Only the `zero` constructor, `Ctx.LiftN n 0 Γ (As ++ Γ)` with `As.length = n`: `cext_z` and
`cext_s` build `As ++ Γ` one entry at a time, counting `n`. Every derivable `cext n G G2` has
`G2` equal to `G` with `n` entries (any expressions) consed on, which is the constructor's
instance with `As` those entries; `Ctx.LiftN.zero` puts no condition on `As`.

### `weakDF` (`spec/lean.mm0`, "Admissible rules")

`deq G e e2 A > cext n G G2 > lift n nz e r > lift n nz e2 r2 > lift n nz A R > deq G2 r r2 R` is
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
  level variable per universe parameter, and no term claims a constant the export lacks; or
  it is a type, constructor or recursor of a stage-B block, which stands as
  `ind_ty (X_D us) i`, `ind_ctor (X_D us) i c` or `ind_rec (X_D us) i v` (the names from the
  export's `all` and constructor lists and `X.rec`, and `X.rec_k` for the recursor of the
  `k`th auxiliary type of a nested block; a recursor with the motive's level first when the
  export's has one more level than the block's; an auxiliary type or its constructor stands
  for nothing, so a statement about one is no type claim);
* a block's data definition `def X_D (us): ind = ind_mk X_blk P T` (doc "The inductive block
  of `X`...") is the export's declaration: `P` has the declared number of parameters, each
  type's type is `Π P. F_i` and each constructor's `Π P. K` with the block's types as
  variables above the parameters, compared with the exported types after their binders'
  type annotations (`outParam`, `optParam`, ...) are consumed as the kernel does (§4); for a
  nested block `ind_mkn X_blk P T N`, `T` has the declared types and then as many auxiliary
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
  `lean0-check` marks: the blocks `nat_D` and `eq_D` and the quotient primitives `quot`,
  `quot_mk`, `quot_lift`, `quot_ind`) stand for `Nat`, `Eq`, `Quot`, `Quot.mk`, `Quot.lift`
  and `Quot.ind` when the export declares them, and are compared the same way (a spec
  declaration the export lacks is ignored);
* an opaque constant is `def c (us): expr = $ cst A (lcons u1 ... lnil) $` over its own
  levels in order, with `A` a `term A: atom` that no other definition uses (a shared or
  aliased atom would make two constants equal by `eeqv_cst` and `eeqv_df`);
* an axiom concluding `closed` or `eeqv` about a constant has the syntactic shape of §4:
  `closed k (c us)` over `(k: nat)` and the levels, or `leqv u u2 > ... > eeqv (c us) (c us2)`
  over the levels and their primed copies, with no other hypotheses;
* every `term` the certificate declares is a constant of sort `atom` (an opaque constant's)
  or `blk` (a block's), the sorts §11's encoding leaves open.

Not checked by it: the other generated axioms, of stage-A blocks and the division-like
literal operations (§4 and §5) and the `_df` typing axioms of opaque constants, which are
argued and generated, not compared with anything in the export; and whether a
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
for `deq G e e2 A`, `⟨ G ⊢ e : A ⟩` for `ty G e A`, `λ A. e` and `Π A. B` for `lam` and `pi`,
`f @ a` for `app`, `#i` for `bvar`, `A :: G` and `[]` for `cons` and `nil`, `a ⊔ b` for
`lmax`, and `≤`, `<` and `≈` for `le`, `lt` and `leqv`. Each has an ASCII form as well,
declared first (`[[ G |- e == e2 : A ]]`, `<< G |- e : A >>`, `\ A. e`, `\Pi A. B`, `\/`, `<=`, `~=`);
the Unicode form is declared last. The delimiters are `( ) . #`.
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

Typing premises (2026-11-05): the core rules `bvar`, `beta`, `eta`, `proofIrrel`, `instDF` and
`inh_i` now state typing with `ty`, the definition of `⟦ G ⊢ e ≡ e : A ⟧`, where they spelled
out the diagonal as Lean4Lean does. The statements are equivalent by unfolding. The generator
converts at each use, which costs 0.38% on `Init.Prelude`.

The generated statements keep the prefix form (`deq G e e2 A`), which MM0 allows for every
term with or without a notation; the statement checker reads only that form. No notation
token looks like an identifier (`[a-zA-Z_][a-zA-Z0-9_]*`), so none can collide with a
generated name.

## 10. The encoding: how the spec departs from Lean4Lean's presentation

The spec transcribes Lean4Lean's `IsDefEq` rules over de Bruijn terms (`VExpr`) as closed
first-order MM0 terms: sorts `nat` (indices), `lvl`, `expr` and `ctx`; the judgment
`deq G e e2 A` (`⟦ G ⊢ e ≡ e2 : A ⟧`); and the side relations `lift`, `inst`, `lookup` and
`closed`, with one axiom per defining clause, which the generator proves syntax-directed.

The file is in three parts (its header). Part I, *Syntax*, declares the sorts and the
relations that are functions or predicates on syntax, defined by clauses recursing on their
inputs; nothing in it mentions `≈` or `⊢`. Part II declares `≈` and `⊢` and the relations
defined over them in the same way (the well-formedness of a block, its elimination level, the
defining equations of the literal operations). Part III states the rules: the 74 axioms
concluding `≈` or `⊢` (and `inh_i`), which are the semantic content and the only axioms whose
truth is at issue in §§2–6; the other 280 are definitions, which `lean0 modes` checks to be the
functions and predicates they are read as (§4, *Functionality*). In a reduction to set theory
the sorts become inductive sets, the clauses of Parts I and II the defining equations of
functions given by the recursion theorem, and Part III the theorems to prove of the model.

The departures from the verbatim presentation:

* **No environment term.** Lean4Lean's `VEnv`, with the `constDF` and `extra` rules, is
  replaced by one MM0 declaration per Lean constant, whose arguments are the constant's
  universe parameters as `lvl` variables. A definition or theorem `c.{u v} : T := v` becomes
  `def c (u v: lvl): expr = $ v $;` with a proved typing theorem `⟨ G ⊢ c u v : T ⟩`, schematic in
  `G`; so δ-unfolding is MM0 unfolding, and universe instantiation (`instL`) is MM0
  substitution of the `lvl` variables. A theorem's body is abstract (only in the MMB), so the
  `.mm0` never shows a proof term. Axioms, opaques, inductive types, constructors, recursors and
  `Quot.*` left to the generated axioms become an atom and a definition,
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
  over their defining equations (`add_eqs`/`nat_add_lit`, ...; `div_eqs`, `gcd_eqs`,
  `bitwise_eqs`, ... for the division-like ones). A **string literal** is translated as its `String.ofList` expansion and
  needs no axiom.
* **Inductives** (§4, stage B): a block is a data term, `def X_D (us): ind = ind_mk X_blk P T`,
  and its types, constructors and recursors are the spec's `ind_ty (X_D us) i`,
  `ind_ctor (X_D us) i c` and `ind_rec (X_D us) i v` (no term per constant; `v` the motive's
  level, `lz` for a small eliminator). The certificate proves `tys_ok G (X_D us)` and
  `ind_wf G (X_D us)`, and from the schema the typing lemma `X_df` of each constant (at any
  equivalent levels, by `eeqv_df`), each recursor rule's iota lemma `X_rec_c_iota` (with the
  exported rule value as a public `def`, checked to be the schema's `rec_rhs`), and for a
  structure the projection and eta lemmas; all with the statements stage A had as axioms.
  A nested block is `ind_mkn b P T N`, the mutual block the kernel checks in its place, with
  the occurrences `N` restored in what it states (§4).
* **Projections and structure eta** (§4): the spec's `proj b i e` for every structure, with
  the block's atom `b` (so that two structures' rules never apply to the same term) and the
  structural `closed`/`lift`/`inst` rules in the spec; typing, reduction and eta are lemmas
  of the schema (stage B) or generated axioms (stage A).
* **`let`** is inlined during translation (derivations memoized on the DAG), and `mdata` is
  erased. Binder names and styles are not represented.

The generated `.mm0` therefore contains, per declaration, its `def` or `term` (or, for a
stage-B block, its atom and data definition), its typing statement, and for opaque constants
the atom and the `constDF` axiom (and `c_eeqv` when a block's data mentions a constant that is
not a `cst`), plus the per-structure and per-recursor lemmas or axioms above;
lemmas made while proving are local to the MMB. §8 says how those statements are tied back
to the export.

## 11. The syntax encoding in set theory (`spec/tg/lean-tg.mm0`; argued here, to be re-audited)

The reduction of the spec to Tarski–Grothendieck set theory (`spec/tg/`) reads every sort of
the spec as a set of finite trees. `spec/tg/lean-tg.mm0` is generated by `scripts/tg-lean.py`
from `spec/lean.mm0` (`--check` fails when it is out of date). It imports the library
(`all.mm0`, whose only axioms are those of `tg.mm0`) and declares the spec's sorts and
constructors verbatim, without notations: every `term` of the spec whose sort is not `wff`,
37 of them (`nat_blk`, `eq_blk` and the quotient primitives included). It also defines a
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
spec's definitions follow verbatim, in prefix form. Each of the spec's 209 clause axioms of
Part I is restated as a theorem with the same name and statement. Theorems about the
program follow, also proved: per relation, that a clause of the program concluding an
`R`-atom is one of `R`'s (`lprog_R_pr`) and inversion (`lrel_R_cases`: a derivable atom is
an instance of one of its clauses, with the premises derivable); and the determinacy of the
computing relations that later proofs need (`lrel_R_det`).

`scripts/tg-lean.py --parse-check` writes every axiom of the spec, as the generator prints
it in prefix form, as a theorem proved by that axiom, and `scripts/test.sh` verifies this.
So the restated statements are the spec's.

**Part II's relations over level equivalence** (`spec/tg/lean-tg2.mm0`, 2026-11-10, generated
by the same script and checked by the same `--check`). The eight relations of Part II whose
clauses need only Part I's relations and `leqv` (`eeqv`, `lseqv`, `ind_eqv`, `ceqv`, `teqv`,
`cseqv`, `ulevel`, `nst_group`; the script finds them) are a second program of the same form
over Part I's least model: a clause's premises of these relations are its premises, and its
other premises are side conditions of its ground instances (an atom of Part I in `lrel`, two
level trees with equal values at every valuation, `lveq`, which is `leqv` at encodings). Each
relation is a definition (its atom is in `lrel2`, the least model), and each of the 29 clause
axioms is a theorem with the spec's statement, followed by `lprog2_R_pr` and inversion
`lrel2_R_cases`. No axioms.

**Part II's relations over the judgment** (`spec/tg/lean-tg3.mm0`, 2026-11-11, generated and
checked likewise). The other 34 relations of Part II (`sty`, `cwf`, `ind_wf`, `nst_ok`,
`large`, `proj_ok`, the literal relations `*_eqs` and `*_dec`, ...) have premises of the
judgment `deq`, which is a term until the model defines it. They are a third program of the
same form over a parameter `J`, a class of judgment atoms standing for `deq`: their side
conditions are atoms of Part I in `lrel`, atoms of the second stratum in `lrel2`, `lveq`, and
judgments in `J`. Each relation is a definition `R_j J`, each of the 48 clause axioms a
theorem `A_j` for every `J` (the spec's statement with `deq` read as `deq_j J`), followed by
`lprog3_R_pr` and inversion `lrel3_R_cases`. The three clauses with more than 30 variables
(`gcd_eqs_i`, `bitwise_eqs_i`, `bitop_eqs_i`) bind them as one sequence, read at the indices
`ixK` (`fv s ixK`), because a proof could not name them one by one. Part II's definition
`fix_fty` is stated here. No axioms. The spec's relations and their clause axioms stay in the
rest file until the judgment is defined, when they become `R_j` at the judgment's atoms.

**Parts II and III** (`spec/tg/lean-tg-rest.mm0`, generated by the same script and checked by
the same `--check`). It imports the model (below) and states the rest of the spec as the spec
states it, in prefix form, with variables named like a library term renamed: Part II's
relations and their clauses and Part III's rules, less what the model declares (a spec term
as a definition, an axiom as a theorem; `lean0 tg-link` checks that each is the spec's
statement). Today that is 36 terms, 1 definition and 101 axioms. They are the spec's own
axioms, so nothing new is trusted. Later layers of the reduction turn them into definitions
and theorems. Until then, the trusted base in TG mode (below) is `tg.mm0`'s 76 axioms, the 48
encoding axioms above and these 101, in place of the spec's 360: Part I's 209 clauses, the 29
clauses of Part II above and the 21 level rules are theorems.

**The model** (`spec/tg/model-levels.mm0`, `spec/tg/model-den.mm0`, 2026-11-09, layer C of
the reduction; `spec/tg/model-meta.mm0` and `spec/tg/model-core.mm0`, 2026-11-10, layers D and I; it imports the strata `lean-tg2.mm0` and
`lean-tg3.mm0` after `model-levels.mm0`). Definitions and theorems only: no axiom, so nothing here is trusted beyond
`tg.mm0` and the encoding. What it changes in TG mode is the reading of the spec's `leqv`,
which is now a definition: a level valuation is a function from `ω` to `ω` (`lvals`), each
level's value is computed by structural recursion on its tree (`lv`: `lz` is 0, `ls` adds
one, `lmax` is `max`, `limax a b` is 0 when `b` is 0 and `max` otherwise, a parameter is
the valuation's value), and `leqv l l2` says the values agree at every valuation. The spec's
21 level rules are theorems about this definition (`leqv_cases` and `leqv_inst` through the
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
  layers: opaque constants, literals, the inductive constants and the quotient primitives
  (`kexa`). It sees the universe, the label, the children and their values. Its value is the
  same at every valuation of the de Bruijn variables, so these constants are closed by
  construction, and it is cut to `u`.
- **The judgments** `mdeq M`, `minh M` quantify over every admissible universe, level
  valuation and satisfying valuation. Symmetry, transitivity, conversion, `sortDF`, `lamDF`,
  `forallEDF`, `proofIrrel` and `inh_i` are theorems for every hook (`msymm` .. `minh_ty`).
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
- **The remaining core rules** (`model-core.mm0`): `bvar`, `appDF`, `beta`, `eta`, `instDF`
  and `weakDF` are theorems for every hook too (`mbvar` .. `mweakDF`), from the above and the
  function-space laws (`cpi_elim_ap`, `clam_ap`, `cpi_eta`). With the eight before, 14 of the
  15 core rules hold in the model for every hook. The fifteenth, `eeqv_df`, holds for every
  hook that is invariant under `eeqv` (`meeqv_df`; `minv M`: a constructor the hook interprets
  denotes the same as every tree it is `eeqv` to), since `eeqv` trees then denote the same
  (`lrel2_eeqv_dt`, by induction on the trees). The hook's definition will have to satisfy
  `minv`.

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
