# Lean0

Lean0 is an experimental tool for verifying Lean 4 proofs against an explicit 
axiomatic presentation of Lean's type theory, using [Metamath 
Zero](https://github.com/digama0/mm0) as a minimal logical framework. A 
modified [nanoda](https://github.com/ammkrn/nanoda_lib) records steps taken in 
checking types and definitional equality; Lean0 then translates these steps to 
a Metamath Zero (MM0) proof. A small and human-inspectable MM0 verifier like 
`mm0-c` can then check the correctness of this proof against a fixed set of 
axioms that aim to encode Lean's type theory. The verification shows that a 
result that nanoda accepted can be derived, step-by-step, from Lean0's axioms.

The Lean0 axioms have a set-theoretic model, constructed using 
Tarski–Grothendieck set theory (with a choice operator) in MM0 itself, 
establishing their consistency relative to that theory. The axioms were 
initially based on [Lean4Lean](https://github.com/digama0/lean4lean)'s 
`IsDefEq` judgment. They add a new schema for inductive types, derived from the 
kernel, since Lean4Lean leaves inductive declarations unspecified. `propext`, 
`Classical.choice`, and `Quot.sound` are also included, and hold in the model. 
The model should also support soundness for arithmetic of every finite order - 
this will need some more work.

Nested inductive types (a prickly topic) are handled more or less as in the 
kernel: the Lean0 axioms allow nested occurrences to be replaced by auxiliary 
types in a larger mutual block, and the types and rules of the recursors to be 
translated back. In the model, an auxiliary type denotes the same set as the 
corresponding nested type, so this procedure is semantically correct.

The basic idea comes from Mario Carneiro, who originally targeted Lean 3 in a 
similar way. 
[`examples/lean.mm1`](https://github.com/digama0/mm0/blob/master/examples/lean.mm1) 
gives an MM1 axiomatization of Lean 3's type theory (levels, typing and 
conversion, a general schema for inductive types including positivity and 
elimination-level conditions, quotients). The idea of using nanoda for tracing 
was [described by Chris Bailey in 
2020](https://leanprover-community.github.io/archive/stream/236449-Program-verification/topic/Projects.html).

## Prior Art

### Independent kernels

Checkers such as lean4checker, nanoda and Lean4Lean's checker implement
Lean's kernel independently. Agreement between implementations provides
evidence against errors specific to one of them.

Lean0 uses nanoda to produce proof certificates, but does not trust nanoda's
verdicts. Because an MM0 verifier checks the derivation against the rules in 
the specification, incorrect proofs produced by nanoda won't verify. For 
example, a conversion returned by an incorrect [cache lookup] still needs a 
derivation; the cached result is not a proof. Similarly, each step of a numeral 
computation must follow from the arithmetic rules, regardless of the result 
returned by the kernel's [bignum library].

[cache lookup]: https://github.com/leanprover/lean4/pull/14806
[bignum library]: https://github.com/leanprover/lean4/pull/14833

### Verified kernels

A verified kernel comes with a proof about the checker across all inputs.
The statement of that proof differs between projects:

- [Lean4Lean] defines a typing and conversion judgment in Lean and is
  developing a proof that its checker is sound for that judgment. Upstream
  leaves inductive declarations unspecified. A [research fork] specifies
  inductive blocks and proves that a successful declaration check preserves
  well-formedness of the environment, assuming injectivity of Π and of
  inductive type formers. The fork describes the work as unaudited and does
  not claim a consistency result.
- [con-leche] proves a semantic property directly, without a separate typing
  judgment: an accepted environment using only Lean's three standard axioms
  has a set-theoretic model. The [proof] uses ZF with a chain of Grothendieck
  universes. The checker differs from Lean's kernel in some checks and in its
  treatment of nested inductive types. Its Rust and x86 counterparts, con-ron
  and [con-agua], are proved to accept only inputs that con-leche accepts.
  The Rust proof uses Aeneas; the assembly proof uses an x86 semantics.

Lean0 instead produces a proof for a *particular export*. While its MM0 
specification adapts Lean4Lean's judgment, it also includes rules for inductive 
blocks, nested inductives, recursors, projections, structure eta, quotients and 
`Nat` literals. A certificate derives typing and conversion judgments from 
those rules, and the certificate can be verified by an MM0 checker, but the 
rust code for generating the certificate is not verified in any meaningful 
sense.

[Lean4Lean]: https://github.com/digama0/lean4lean
[research fork]: https://github.com/typhdotcom/lean4lean
[con-leche]: https://github.com/leanprover/con-leche
[proof]: https://leanprover.github.io/con-leche/con-leche-proof-idea.html
[con-agua]: https://github.com/leanprover/con-agua

### lean2dk

[lean2dk] translates Lean proofs into Dedukti, following [Lean4Less].
Dedukti checks conversion by rewriting. This relies on the rewrite engine and
on confluence and type preservation for the encoding's rules. [Blanqui and
Vaishnav] give a paper proof for the representation of conversion and report
tests on selected files and small mathematical libraries. They list bignum
arithmetic and larger developments as future work.

Lean0 records conversion steps in the proof object instead. This increases
certificate size but does not require a Lean-specific conversion procedure
in the verifier.

[lean2dk]: https://github.com/Deducteam/lean2dk
[Lean4Less]: https://rish987.github.io/files/lean4less.pdf
[Blanqui and Vaishnav]: https://arxiv.org/abs/2609.24604

## Setup

- **Lean0:** Build with `nix build .#lean0`, or run the CLI with
  `nix run .#lean0 -- ...`. To build with Cargo, run
  `scripts/nanoda.sh apply` followed by `cargo build --release`. The script
  prepares the patched nanoda source in `build/nanoda`; the resulting Lean0
  binary is `target/release/lean0`.
- **MM0 verifier:** Use `nix build .#mm0-c` or `nix build .#mm0-zig`.
  The flake builds `mm0-c` with increased capacity for large certificates.
  `mm0-zig` is distributed with [Aufbau](https://github.com/gleachkr/Aufbau).
- **lean4export:** Build the exporter with the Lean version used by the
  project whose `.olean` files it will read (see below).

For development, `nix develop` provides Rust, elan, perf, both MM0 verifiers
and Aufbau's `abc` for the hand-written proofs. Run `scripts/test.sh` in that
environment. It builds the pinned exporter in `tests/lake/`, verifies
certificates with both verifiers and checks the modes of the specification's
relations. Negative tests cover altered certificates, a corrupted export,
illegal inductive declarations and overlapping clauses in the specification.

## Use

### Export theorems from a Lake project

Lean0 reads export format 3.1.x and is tested with Lean v4.35.0. For that
version, add the following dependency to `lakefile.toml`:

```toml
[[require]]
name = "lean4export"
git = "https://github.com/leanprover/lean4export"
rev = "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe"
```

For `lakefile.lean`, use:

```lean
require lean4export from git
  "https://github.com/leanprover/lean4export" @
  "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe"
```

For another Lean release, select the corresponding toolchain revision of
lean4export. To export two theorems and their dependencies:

```sh
lake update lean4export
lake build
lake exe lean4export MyProject -- MyProject.foo MyProject.bar > slice.ndjson
```

Omit `--` and the theorem names to export the entire module and its imports.
To leave the project unchanged, build lean4export in a separate checkout
with `lake build`, then invoke its binary from the project with `lake env`:

```sh
lake env /path/to/lean4export/.lake/build/bin/lean4export \
  MyProject -- MyProject.foo MyProject.bar > slice.ndjson
```

### Generate and verify a certificate

```sh
lean0 gen slice.ndjson OUT slice
lean0 joined OUT/slice.mm0 > OUT/slice.joined.mm0
mm0-c OUT/slice.mmb < OUT/slice.joined.mm0
lean0 check slice.ndjson OUT/slice.mm0
```

`gen` writes the statements (`.mm0`) and proofs (`.mmb`). `joined` combines
the specification and statements into the input for the verifier. `mm0-c`
checks the proofs against that text; `mm0-zig` can be used with the same
arguments and input. `lean0 check` compares the statements with the export
and prints the top-level theorems in Lean syntax.

If `gen` reports a missing constant in the defining equations for a `Nat`
operation, add the constant to the export list. For example, the derivations
for `Nat.div` and `Nat.mod` require `instDecidableEqBool`. Unsupported
declarations cause generation to fail. With `--keep-going`, Lean0 skips the
unsupported declarations and those that depend on them.

### Certify a standalone module

```sh
scripts/certify.sh tests/lean/Induct.lean
```

This compiles the module, exports it, generates a certificate, runs both
verifiers and checks the statements. Output for this example is in
`build/gen/induct/`. A comment of the form `-- lean0-export: NAME...` in the
module restricts the export to the named declarations and their dependencies.
The script looks for `lean4export`, `mm0-c` and `mm0-zig` on `PATH`; use
`LEAN4EXPORT`, `MM0_C` and `MM0_ZIG` to specify other locations.

### Split a large export

For exports such as `Init`, Lean0 can generate certificates in parts. The
following example uses the Cargo release binary and a fresh output directory.
First create the export:

```sh
mkdir -p build/lean OUT
(
  cd build/lean || exit 1
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
  printf 'import Init\n' > InitAll.lean
  lean -o InitAll.olean InitAll.lean &&
    LEAN_PATH="$PWD" lean4export InitAll > initall.ndjson
)
```

Then start the verifier and generate the parts:

```sh
export_file=build/lean/initall.ndjson
scripts/check-parts.sh --follow --delete --export "$export_file" OUT init &
verifier=$!
target/release/lean0 gen "$export_file" OUT init \
  --parts 64 --jobs 8 --max-pending 8
wait "$verifier"
```

`--delete` removes each `.mmb` file after checking, including rejected parts.
The `.mm0` statements remain in `OUT/init.partK.mm0`; verification results
are recorded in `OUT/init.check.log`. With eight workers, `--max-pending 8`
limits the number of parts on disk to about 16. `--balance STATS` uses a
previous run's statistics to choose part boundaries. Allow for `mm0-zig`'s
4 GiB input limit: one part exceeded it in a 32-part `Init` run and four
exceeded it in a 192-part `Std` run. Use more parts or adjust their balance
when checking with that verifier.

To collect statistics without writing certificates:

```sh
lean0 gen EXPORT OUT NAME --stats-only --keep-going --jobs 8
```

Set `LEAN0_PROGRESS=1` for per-declaration progress or `LEAN0_COSTS=1` for a
breakdown of proof size.

## Layout

- `spec/lean.mm0` imports the specification: `lean-core.mm0` (levels,
  expressions, contexts and judgments), `lean-ind.mm0` (inductives),
  `lean-quot.mm0` (quotients) and `lean-lit.mm0` (`Nat` literals).
  `lean0 spec` prints the combined text. `spec/lib.auf` contains derived
  rules; `spec/examples/` contains hand-written certificates.
- `spec/tg/` contains the Tarski–Grothendieck library and the model.
  `tg.mm0` gives the set-theoretic basis. `lean-tg.mm0`, `lean-tg2.mm0` and
  `lean-tg3.mm0` encode the syntax and relations; `scripts/tg-lean.py`
  generates these files. The `model-*.mm0` files interpret the judgment and
  prove the specification's rules. `lean-tg-rest.mm0` adds no further Lean0
  axioms. Run `scripts/tg-check.sh spec/tg/lean-tg-rest.mm0` to check the
  library. `scripts/certify.sh --tg` uses `lean0 tg-link` and
  `lean0 joined --tg` to verify a certificate against the model.
- `lean0/` contains the elaborator, generator and CLI. `lean0-check/`
  contains the statement checker, the embedded specification and model
  library, and the code that prepares the verifier's input text.
- `patches/nanoda_lib.patch` adds tracing hooks and exposes the required
  nanoda interfaces. The flake and `scripts/nanoda.sh` apply it to the same
  pinned revision.
- `mm0kit/` implements MM0 terms and proofs, provers for levels and auxiliary
  relations, the MMB writer, merging of parts and linking to the model.
- `tests/lean/` contains standalone test modules; `tests/lake/` is an
  example Lake project. `scripts/` contains the build, certification and test
  scripts.
- [`notes/audit-lean-mm0.md`](notes/audit-lean-mm0.md) documents the
  soundness argument, and differences from Lean4Lean.
