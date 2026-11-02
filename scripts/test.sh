#!/usr/bin/env bash
# Check the hand-written certificates (spec/examples) and the generated ones (tests/lean) with
# both verifiers, then run negative tests.
#
# An MMB file restates every statement, and the verifiers compare each with the .mm0 file, so
# editing a statement in the .mm0 alone is rejected before any proof is looked at. Those
# "statement mismatch" tests only show that the statements are compared. The tamper tests show
# that the proofs are checked: lean0 changes a statement in both files and keeps the proofs.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
# the verifiers from PATH (the dev shell has the flake's), unless given
MM0_ZIG="${MM0_ZIG:-mm0-zig}"
MM0_C="${MM0_C:-mm0-c}"
# lean4export at the revision lean0 uses: the one tests/lake builds (a git dependency there, as
# the README has users add it), unless given
if [ -z "${LEAN4EXPORT:-}" ]; then
  (cd tests/lake && lake build lean4export > /dev/null) || { echo "FAIL: building lean4export in tests/lake"; exit 1; }
  LEAN4EXPORT="$root/tests/lake/.lake/packages/lean4export/.lake/build/bin/lean4export"
fi
export MM0_C MM0_ZIG LEAN4EXPORT
# the crates build against the patched nanoda in build/nanoda
scripts/nanoda.sh apply > /dev/null
fail=0

# accepted_by MMB MM0: how many of the two verifiers accept.
accepted_by() {
  local n=0
  for v in "$MM0_ZIG" "$MM0_C"; do
    "$v" "$1" < "$2" > /dev/null 2>&1 && n=$((n + 1))
  done
  echo "$n"
}

for mm0 in spec/examples/*.mm0; do
  echo "== ${mm0#spec/examples/}"
  scripts/check.sh "$mm0" "${mm0%.mm0}.auf" || fail=1
done

echo "== mm0kit self-test"
cargo run -q --release -p mm0kit --example selftest -- spec/lean.mm0 build/out/selftest.mm0 build/out/selftest.mmb > /dev/null
[ "$(accepted_by build/out/selftest.mmb build/out/selftest.mm0)" = 2 ] && echo "selftest: ok" || { echo "FAIL: selftest"; fail=1; }

for lean in tests/lean/*.lean; do
  echo "== ${lean#tests/lean/}"
  scripts/certify.sh "$lean" > /dev/null || { echo "FAIL: $lean"; fail=1; }
done

# A Lake project, the way the README's "Theorems from a Lake project" does it: export a slice
# with lean4export as a dependency, then gen, joined, both verifiers and check, whose summary
# must list exactly the two theorems asked for.
echo "== a Lake project (tests/lake)"
lk=build/gen/lake; rm -rf "$lk"; mkdir -p "$lk"
if (cd tests/lake && lake build > /dev/null 2>&1 && lake exe lean4export Demo -- Demo.double_comm Demo.Tree.size_pos) > "$lk/demo.ndjson" \
  && target/release/lean0 gen "$lk/demo.ndjson" "$lk" demo > /dev/null 2>&1 \
  && target/release/lean0 joined "$lk/demo.mm0" > "$lk/demo.joined.mm0" \
  && [ "$(accepted_by "$lk/demo.mmb" "$lk/demo.joined.mm0")" = 2 ] \
  && target/release/lean0 check "$lk/demo.ndjson" "$lk/demo.mm0" > "$lk/check.txt" \
  && grep -q 'Lean theorem `Demo.Tree.size_pos`' "$lk/demo.mm0" \
  && [ "$(grep '^  [a-z]* ' "$lk/check.txt" | cut -d' ' -f3,4 | tr '\n' ' ')" = "theorem Demo.double_comm theorem Demo.Tree.size_pos " ]; then
  echo "lake: ok (Demo.double_comm, Demo.Tree.size_pos and their dependencies)"
else echo "FAIL: lake project"; fail=1; fi
rm -rf "$lk"

# `lean0 check` ties the statements to the export: edits to a stated type, a definition's body,
# a theorem (stated as an axiom) or a doc comment's Lean name must each be caught.
echo "== negative tests: statements that do not say what the export says"
stmt_neg() {
  local edit="$1" f=build/gen/initsample/initsample.mm0
  sed -e "$edit" "$f" > build/gen/initsample/neg.mm0
  if cmp -s "$f" build/gen/initsample/neg.mm0; then echo "FAIL (edit did nothing): $edit"; fail=1; return 0; fi
  if target/release/lean0 check build/lean/initsample.ndjson build/gen/initsample/neg.mm0 > /dev/null; then
    echo "FAIL (accepted): $edit"; fail=1
  else echo "rejected as expected: $edit"; fi
}
stmt_neg '0,/^theorem rfl_ty/s/(srt u) (pi (bvar z)/(srt u) (pi (bvar (s z))/'
stmt_neg 's/^def rfl (u: lvl): expr = \$ lam (srt u) (lam (bvar z)/def rfl (u: lvl): expr = $ lam (srt u) (lam (bvar (s z))/'
stmt_neg '/^theorem Eq_symm_ty/s/^theorem/axiom/'
stmt_neg 's/Lean definition `rfl`/Lean definition `rfl2`/'
rm -f build/gen/initsample/neg.mm0

# Sharded generation (`--jobs`) must give the same statements, and a certificate both accept.
echo "== sharded generation"
sh_out=build/gen/sharded; rm -rf "$sh_out"
if target/release/lean0 gen build/lean/initsample.ndjson "$sh_out" initsample --jobs 3 > /dev/null 2>&1 \
  && cmp -s "$sh_out/initsample.mm0" build/gen/initsample/initsample.mm0 \
  && target/release/lean0 joined "$sh_out/initsample.mm0" > "$sh_out/initsample.joined.mm0" \
  && [ "$(accepted_by "$sh_out/initsample.mmb" "$sh_out/initsample.joined.mm0")" = 2 ]; then
  echo "sharded: ok (3 shards, same statements as sequential)"
else echo "FAIL: sharded generation"; fail=1; fi
rm -rf "$sh_out"
# Separate certificates (`--parts`): scripts/check-parts.sh verifies each part, with both
# verifiers, against the text `lean0 joined` builds (the earlier parts' theorems as axioms).
echo "== multi-part certificate"
if target/release/lean0 gen build/lean/initsample.ndjson "$sh_out" initsample --parts 3 > /dev/null 2>&1 \
  && scripts/check-parts.sh --export build/lean/initsample.ndjson "$sh_out" initsample > /dev/null 2>&1; then
  echo "parts: ok (3 certificates)"
else echo "FAIL: multi-part certificate"; fail=1; fi
# A part's statements are restated by the later parts from its own .mm0, so changing one there
# (a theorem stated as an axiom) must be rejected.
sed -i '0,/^theorem /s//axiom /' "$sh_out/initsample.part1.mm0"
if scripts/check-parts.sh "$sh_out" initsample > /dev/null 2>&1; then
  echo "FAIL (accepted): parts with an edited statement"; fail=1
else echo "rejected as expected: parts with an edited statement"; fi
rm -rf "$sh_out"
# Made and checked together, deleted as they are verified, with at most one finished part
# waiting (`--max-pending`), as for Std.
mkdir -p "$sh_out"
timeout 600 scripts/check-parts.sh --follow --delete "$sh_out" initsample > /dev/null 2>&1 &
checker=$!
if target/release/lean0 gen build/lean/initsample.ndjson "$sh_out" initsample --parts 3 --jobs 1 --max-pending 1 > /dev/null 2>&1 \
  && wait "$checker" && [ "$(grep -c '^ok: part' "$sh_out/initsample.check.log")" = 3 ] \
  && ! ls "$sh_out"/initsample.part*.mmb > /dev/null 2>&1; then
  echo "parts, checked as made: ok (3 parts, each deleted once verified)"
else
  echo "FAIL: parts checked as made"; fail=1
  kill "$checker" 2>/dev/null || true
fi
rm -rf "$sh_out"

# mismatch OUT SED-EXPR: OUT.mmb must fail against OUT.joined.mm0 edited by SED-EXPR.
mismatch() {
  local out="$1" expr="$2"
  sed -e "$expr" "$out.joined.mm0" > "$out.neg.mm0"
  if cmp -s "$out.joined.mm0" "$out.neg.mm0"; then
    echo "FAIL (edit did nothing): $out: $expr"; fail=1; return 0
  fi
  if [ "$(accepted_by "$out.mmb" "$out.neg.mm0")" = 0 ]; then echo "rejected as expected: $(basename "$out"): $expr"
  else echo "FAIL (accepted): $out: $expr"; fail=1; fi
}

# tamper MODULE WANT OPTION NAME: regenerate MODULE's certificate with `lean0 gen OPTION NAME`;
# WANT is `rejected` or `accepted` (both verifiers must agree).
tamper() {
  local mod="$1" want="$2" opt="$3" what="$4" out="build/gen/tamper"
  rm -rf "$out"; mkdir -p "$out"
  target/release/lean0 gen "build/lean/$mod.ndjson" "$out" t "$opt" "$what" > /dev/null 2>&1 \
    || { echo "FAIL: lean0 $opt $what"; fail=1; return 0; }
  local got
  case "$(accepted_by "$out/t.mmb" "$out/t.joined.mm0")" in
    0) got=rejected ;; 2) got=accepted ;; *) echo "FAIL: verifiers disagree: $mod $opt $what"; fail=1; return 0 ;;
  esac
  if [ "$got" = "$want" ]; then echo "$got as expected: $mod $opt $what"
  else echo "FAIL ($got, expected $want): $mod $opt $what"; fail=1; fi
}

echo "== negative tests: statement mismatch (hand-written certificates)"
mismatch build/out/church 's/(app (csucc u) (czero u)) (cone u) (cnat u)/(app (csucc u) (czero u)) (czero u) (cnat u)/'
mismatch build/out/core 's/theorem id_inh (u: lvl): \$ inh nil (pi (srt u) (pi (bvar z) (bvar (s z))))/theorem id_inh (u: lvl): $ inh nil (pi (srt u) (pi (bvar z) (bvar z)))/'
mismatch build/out/church 's/def cone (u: lvl): expr = \$ lam (srt u) (lam (pi v0 v1) (lam v1 (app v1 v0))) \$;/def cone (u: lvl): expr = $ lam (srt u) (lam (pi v0 v1) (lam v1 v0)) $;/'

echo "== negative tests: tampered statements, original proofs (generated certificates)"
# A false statement with the original proof.
tamper core rejected --tamper-theorem two_add_two_ty
tamper core rejected --tamper-theorem pt_lvl_ty
tamper deflevels rejected --tamper-theorem tag_lvl_ty
tamper induct rejected --tamper-theorem two_add_two_ty
tamper induct rejected --tamper-theorem quot_ex_ty
# Rules the proofs depend on: a false premise makes every use fail ...
for ax in beta eta proofIrrel sortDF lmax_comm Pt_df; do tamper core rejected --tamper-axiom "$ax"; done
for ax in Eq_rec_refl_iota MyNat_rec_succ_iota MyList_rec_cons_iota Prod_eta PUnit_eta Sigma_eta \
          Prod_proj_0_mk And_proj_1_df Prod_proj_inst Quot_lift_mk; do
  tamper induct rejected --tamper-axiom "$ax"
done
# ... and rules they do not use are harmless, which shows the test can tell the difference.
tamper induct accepted --tamper-axiom And_eta
tamper induct accepted --tamper-axiom eta
# Literals: the generated literal axioms and the binary-arithmetic relations.
tamper lit rejected --tamper-theorem lit_mul_big_ty
tamper lit rejected --tamper-theorem dbl_ex_ty
for ax in Nat_lit_zero Nat_lit_succ Nat_add_lit Nat_mul_lit Nat_sub_lit0 Nat_beq_lit_gt Nat_ble_lit_gt Nat_pow_lit \
          Nat_shiftLeft_lit closed_lit bsucc_d1 badd_11 baddc_11 bmul_d1 bpow_d1 bdbl_d1; do
  tamper lit rejected --tamper-axiom "$ax"
done
tamper lit accepted --tamper-axiom bxor_11
# Substitution (typing handles).
for ax in instDF cinst_z cinst_s; do tamper lit rejected --tamper-axiom "$ax"; done

echo "== negative tests: a corrupted export"
# two_add_two given the statement of and_comm': nanoda must reject it, so no certificate.
bad="build/gen/bad"
rm -rf "$bad"; mkdir -p "$bad"
python3 scripts/mutate-export.py build/lean/core.ndjson "$bad/bad.ndjson" two_add_two "and_comm'"
if target/release/lean0 gen "$bad/bad.ndjson" "$bad" bad > /dev/null 2>&1 || [ -e "$bad/bad.mmb" ]; then
  echo "FAIL: a corrupted export was certified"; fail=1
else
  echo "rejected as expected: corrupted export"
fi

[ "$fail" = 0 ] && echo "all tests passed" || { echo "SOME TESTS FAILED"; exit 1; }
