# Lean0

Lean0 is an experimental tool for verifying Lean 4 proofs against an explicit 
axiomatic presentation of Lean's type theory (about 900 lines, half of it the 
schema for inductive types), using [Metamath 
Zero](https://github.com/digama0/mm0) as a minimal logical framework. It uses a 
modified [nanoda](https://github.com/ammkrn/nanoda_lib) to record the steps 
involved in checking types and definitional equality, and then translates these 
to explicit proof steps within an `.mmb` binary (a Metamath Zero proof 
certificate), which can then be verified against the axiomatic presentation of 
Lean 4 using a small and inspectable MM0 verifier like `mm0-c`.

The idea originates with Mario Carneiro, as a project targeting Lean 
3. [`examples/lean.mm1`](https://github.com/digama0/mm0/blob/master/examples/lean.mm1) 
gives an MM1 axiomatization of Lean 3's type theory (levels, typing and 
conversion, a general schema for inductive types including positivity and 
elimination-level conditions, quotients). The idea of using nanoda for tracing 
was [described by Chris Bailey in 
2020](https://leanprover-community.github.io/archive/stream/236449-Program-verification/topic/Projects.html).

Lean0 implements this idea for Lean 4, with axioms based on 
[Lean4Lean](https://github.com/digama0/lean4lean)'s `IsDefEq` judgment, and a 
schema for inductive types (positivity, universes, the elimination level, the 
recursor's type and rules, projections and structure eta) transcribed from the 
kernel, since Lean4Lean leaves inductive declarations unspecified.

Nested inductive types are certified as the kernel does them: as the mutual 
block with auxiliary types that the kernel checks in their place, with the 
nested occurrences restored in what is stated. The accelerated `Nat` 
operations are rules of the spec over the defining equations Lean4Lean checks 
(a certificate derives `Nat.add x 0 ≡ x` and `Nat.add x (y+1) ≡ (Nat.add x y)+1` 
once, and the arithmetic itself is proved bit by bit; for division, modulus, 
gcd and the bitwise operations the equations are those of the fuel and 
well-founded recursions Lean defines them by, with the conditionals and 
decision procedures as variables). Quotients and the tie between literals and 
`Nat` are part of the spec.

## Trusted Base

In order to trust that theorems certified by lean0 are correct, you need to 
trust:

- an MM0 verifier. The flake builds mm0-c with larger fixed
  capacities (name tries, expression store, input buffer, unify stack), since 
  large certificates overflow the defaults; every access to them is 
  bounds-checked;
- `spec/lean.mm0`, a transcription of Lean4Lean's typing judgment with a few 
  pragmatic extensions (binary Nat literals, two admissible rules, 
  side-relation shortcuts, the quotient primitives with their types and 
  reduction rules), and the schema for inductive types: a declaration 
  is a term of the spec, the certificate proves it legal (positivity, 
  universes, elimination level), and the recursor's type and rules, 
  projections and eta are derived from it. Its soundness argument is 
  `notes/audit-lean-mm0.md` §4; the kernel's recursors are compared with the 
  derived ones on every block, and Lean's `Nat` and `Eq` are stated in the 
  spec and compared with the export's. This is where the kernel's soundness bugs have 
  been (nested inductives: [#14576](https://github.com/leanprover/lean4/issues/14576),
  [#14616](https://github.com/leanprover/lean4/pull/14616); the `Prop` test
  guarding elimination and projection:
  [#14613](https://github.com/leanprover/lean4/pull/14613),
  [#14807](https://github.com/leanprover/lean4/pull/14807),
  [#14843](https://github.com/leanprover/lean4/pull/14843));
- axioms generated per declaration for the few inductive types the schema 
  leaves out (those whose shape the kernel reads through `whnf`: recursor 
  rules, projections and eta, with the declaration's legality unchecked), one 
  per accelerated `Nat` operation whose defining equations could not be 
  derived (`Nat.add` on numerals is addition, and so on; none in Init), and 
  one per 
  opaque constant that an inductive declaration mentions at its universe 
  levels (the constant at equivalent levels is the same expression). `lean0 
  gen` reports how many blocks the schema left to these axioms, and the 
  assumptions are inspectable in the generated `.mm0` file;
- that the `.mm0` file the verifier reads is in fact the spec followed by the 
  certificate's statements (the verification targets). `lean0 joined` generates 
  this file, and its output can be checked by inspection.

In order to additionally trust that a certified theorem is the Lean theorem it 
names, with the statement Lean gives it, you need to trust:

- `lean4export`;
- `nanoda`'s export parser;
- either `lean0`'s translation of declarations into MM0 statements, or `lean0 
  check` (the `lean0-check` crate, about 900 lines, independent of the 
  generator), which reads `.mm0` statements and each inductive block's 
  declaration back into Lean expressions (a nested block's with its 
  occurrences restored) and compares them with the export (of the generated 
  axioms above it checks only the shape of the syntactic ones, `closed` and 
  `eeqv`).

## Prior Art

Where does this fit into current approaches to higher assurance Lean 
verification?

### Independent Kernels

Independent kernels (lean4checker, nanoda, Lean4Lean's checker) guard against 
bugs in Lean's kernel through redundancy. They implement an alternative kernel, 
with functionality similar to the original kernel, in the expectation that it 
will not have the same bugs as the original kernel. That requires a second 
program of about the same size, with implementation choices potentially guided 
by existing kernels.

A Lean0 certificate provides a different kind of assurance, by connecting 
kernel output to a direct axiomatization of the underlying type theory.
For example, no certificate could been generated for a buggy proof dependent on 
issues with Lean's order-dependent conversion cache 
([#14806](https://github.com/leanprover/lean4/pull/14806)), since there is no 
derivation for a wrong conversion. Similarly, a certificate could not have been 
generated for the proof of `False` through literal arithmetic 
([#14833](https://github.com/leanprover/lean4/pull/14833)) that exploited a GMP 
bug, since a certificate proves each numeral computation bit by bit from the 
spec's rules rather than stating its result.

### lean2dk

Another project in a similar spirit to lean0 is lean2dk, which translates 
Lean proofs to Dedukti ([Blanqui and Vaishnav, 
2026](https://arxiv.org/abs/2609.24604);
[lean2dk](https://github.com/Deducteam/lean2dk), following
[Lean4Less](https://rish987.github.io/files/lean4less.pdf)). This approach also 
moves Lean into a small checker. As of the paper, the Dedukti translation has 
run on "specific test files and small mathematical libraries", with bignum 
arithmetic and scale as future work.

Dedukti is the λΠ-calculus *modulo rewriting*: conversion is done by its 
checker's rewrite engine, so the trusted base includes that engine and the 
confluence and type preservation of the encoding's rules. The correctness of 
the conversion representation does have a paper proof, but has not been 
formally verified. Lean0 carries conversion as explicit derivation steps 
instead. This means certificates are quite large, but the verifier only needs 
to check proof steps in a totally generic way.

## Status

With the trust list above, conversion and typing have been certified for all 
of Lean's `Init` and all of `Std`:

- `Init` (59,423 declarations): 32 certificates, 107.1 GB, generated in 69 
  minutes on 8 cores, each verified and deleted as it was made. 605 of its 607 
  inductive types are certified by the schema (the other two are nested); 577 
  generated axioms remain, 521 of them the typing and closedness of 261 opaque 
  constants and Lean axioms (`IO` and `Float` primitives, mostly), the rest 
  the literal operations, the two nested types and level congruence for 24 
  opaque constants in inductive declarations;
- `Std` (103,256 declarations with `Init`): 195 certificates, 335.7 GB, 
  generated in 3 hours on 8 cores. This run predates the schema (it has the 
  inductive types as generated axioms) and is not redone yet. One declaration
  (`goCache_Inv_of_Inv._mutual`, in `Std`'s bit-blaster) has its statements but 
  no proof: its proof alone is past the MMB format's 4 GiB of table data.

Every conversion step nanoda took over those 103,256 declarations has a 
derivation in the spec. The everyday case is smaller: chosen theorems of a Lake 
project with their dependencies, for example `tests/lake/`'s two theorems (102 
declarations in all), can be certified in a fraction of a second (5 MB).

**Scale.** Certificates are large because conversion is explicit. Mathlib has 
several times `Std`'s declarations with far heavier proof terms, so a linear
guess puts it in the terabytes, optimistically. More work needs to be done on 
efficiently handling these certificates, perhaps compressing them.

## Setup

To use lean0, you need:

- **lean0**, built with `nix build .#lean0` (or `nix run .#lean0 -- ...`), or
  `scripts/nanoda.sh apply && cargo build --release` (`target/release/lean0`). 
  The `nanoda.sh` script builds a patched nanoda in `build/nanoda`, which the 
  crates then build against.
- **an MM0 verifier**: mm0-c (`nix build .#mm0-c`, the flake's build with the 
  larger capacities large certificates need) or mm0-zig from 
  [Aufbau](https://github.com/gleachkr/Aufbau) (`nix build .#mm0-zig`).
- **lean4export**, built with your project's Lean (see "Theorems from a Lake 
  project" below).

**For development**, `nix develop` has Rust, elan, perf and the pinned verifiers (mm0-c,
mm0-zig, and Aufbau's `abc` for the hand proofs). Then `scripts/test.sh` runs everything, with
both verifiers and the negative tests (tampered certificates, a corrupted export, and
hand-made illegal inductive declarations, which the schema must reject), and prints "all
tests passed". It builds lean4export
in `tests/lake`, as a Lake dependency at the pinned revision.

## Use

For an export `x.ndjson` from lean4export:

```sh
lean0 gen x.ndjson OUT x                      # OUT/x.mm0 (statements), OUT/x.mmb (proofs)
lean0 joined OUT/x.mm0 > OUT/x.joined.mm0     # the spec and the statements
mm0-c OUT/x.mmb < OUT/x.joined.mm0            # the proofs prove the statements
mm0-zig OUT/x.mmb < OUT/x.joined.mm0          # (a second verifier)
lean0 check x.ndjson OUT/x.mm0                # the statements say what the export says,
                                              # and the top-level theorems in Lean syntax
```

lean4export reads the project's `.olean` files, so it has to be built with the 
project's own Lean version. So to generate an export, add lean4export to the 
project at the revision corresponding to the lean version: lean4export has a 
"bump toolchain" commit for each Lean release, and 
`5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` is the one for Lean v4.35.0, the 
version lean0 is tested with. In `lakefile.toml`:

```toml
[[require]]
name = "lean4export"
git = "https://github.com/leanprover/lean4export"
rev = "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe"
```

(in a `lakefile.lean`: `require lean4export from git
"https://github.com/leanprover/lean4export" @ "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe"`).
Then export the theorems you want certified, and continue with the steps above:

```sh
lake update lean4export
lake build
lake exe lean4export MyProject -- MyProject.foo MyProject.bar > slice.ndjson
```
The names after `--` restrict the export to those declarations and what they 
depend on (typically tens to a few thousand declarations, certified in 
seconds); without them the modules and everything they import are exported. To 
leave the project unchanged instead, build lean4export separately at that 
revision (`lake build` in a checkout) and run it from the
project with `lake env PATH/TO/lean4export/.lake/build/bin/lean4export 
MyProject -- ...`. lean0 reads export format 3.1.x. On a newer Lean, a 
declaration using something lean0 does not support makes `lean0 gen` fail (or, 
with `--keep-going`, skip it and what depends on it); it cannot make it certify 
something false. `tests/lake/` is an example, certified by `scripts/test.sh`.

### Additional usage examples

**The pipeline** end to end (compile, export, generate, verify with both 
verifiers, check the statements; lean4export, mm0-c and mm0-zig on PATH, or in 
`LEAN4EXPORT`, `MM0_C`, `MM0_ZIG`):

```sh
scripts/certify.sh tests/lean/Induct.lean      # outputs in build/gen/induct/
```

A `-- lean0-export: NAME...` line in the module restricts the export to those 
declarations and what they depend on.

**A large export**, such as all of `Init`, as several certificates that are 
verified, and deleted, as they are made (so they never all have to be on disk):

```sh
cd build/lean && printf 'import Init\n' > InitAll.lean \
  && lean +leanprover/lean4:v4.35.0 -o InitAll.olean InitAll.lean \
  && LEAN_PATH=$PWD lean4export InitAll > initall.ndjson && cd ../..
scripts/check-parts.sh --follow --delete --export build/lean/initall.ndjson OUT init &
target/release/lean0 gen build/lean/initall.ndjson OUT init --parts 32 --jobs 8 --max-pending 8
```

Each part `OUT/init.partK` keeps its statements (`.mm0`), and 
`OUT/init.check.log` records the verification. `--max-pending 8` holds the next 
part while 8 finished ones wait to be verified and deleted, so at most about 16 
parts are on disk at once. `--balance STATS` divides the declarations by an 
earlier run's stats file. mm0-zig reads files of at most 4 GiB, so give large 
exports enough parts (`Init` in 32 parts has one larger; `Std` in 192 has 
four).

**A census** (stats only, no certificate): `lean0 gen EXPORT OUT NAME --stats-only
--keep-going --jobs 8`, with `LEAN0_PROGRESS=1` for a line per declaration and `LEAN0_COSTS=1`
for where the proof bytes go.

## Layout

- `spec/lean.mm0`: the trusted MM0 spec of LeanTT; `spec/lib.auf`: derived rules (untrusted);
  `spec/examples/`: hand-proven certificates
- `lean0/`: the elaborator and generator, and the `lean0` binary (`src/bin/lean0/`)
- `lean0-check/`: the trusted side of `lean0`: the statement checker, the text the verifiers
  check against, and the embedded spec
- `patches/nanoda_lib.patch`: our changes to [nanoda](https://github.com/ammkrn/nanoda_lib),
  the tracing hook and some visibility, applied to a pinned upstream commit by
  `scripts/nanoda.sh apply` (into `build/nanoda`) and by the flake
- `mm0kit/`: MM0 terms and proofs, provers for the spec's side relations and levels, the MMB
  writer and the merge of sharded output
- `tests/lean/`: Lean modules certified by `scripts/test.sh`; `tests/lake/`: a Lake project
  certified the way the README describes
- `scripts/`: `nanoda.sh`, `certify.sh`, `check-parts.sh`, `test.sh`, `fetch-refs.sh` (the
  verifiers and lean4export come from PATH, or from `MM0_C`, `MM0_ZIG`, `ABC`, `LEAN4EXPORT`)
- `notes/audit-lean-mm0.md`: the soundness argument for the spec and every generated axiom,
  and how the encoding departs from Lean4Lean's presentation
