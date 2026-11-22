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

# The TG library with the encoding of the spec's syntax (spec/tg/lean-tg.mm0, generated from
# the spec) and the rest of the spec over it (lean-tg-rest.mm0, axioms for now): in sync with
# the spec, and every theorem proved. Its MMB file is the start of every certificate in TG mode
# (`certify.sh --tg` below).
echo "== spec/tg (the set-theory library and the syntax encoding)"
if scripts/tg-lean.py --check && tg=$(scripts/tg-check.sh spec/tg/lean-tg-rest.mm0) && echo "$tg" && [[ "$tg" == *"; 0 admitted with sorry!; 0 warnings)" ]]; then :; else echo "FAIL: spec/tg"; fail=1; fi
# The generator's notation parser: every axiom of the spec in prefix form, proved by the axiom.
pc=build/tg/parsecheck
if scripts/tg-lean.py --parse-check $pc && "${ABC:-abc}" compile $pc/check.mm0 $pc/check.auf $pc/check.mmb \
    && "${ABC:-abc}" join $pc/check.mm0 > $pc/check.joined.mm0 && "$MM0_C" $pc/check.mmb < $pc/check.joined.mm0; then
  echo "spec/tg: the notation parser restates the spec's $(grep -c '^theorem' $pc/check.mm0) axioms"
else echo "FAIL: the notation parser (scripts/mm0math.py)"; fail=1; fi

echo "== mm0kit self-test"
# the spec as one text (spec/lean.mm0 imports its four files)
cargo run -q --release --bin lean0 -- spec > build/out/lean.mm0
cargo run -q --release -p mm0kit --example selftest -- build/out/lean.mm0 build/out/selftest.mm0 build/out/selftest.mmb > /dev/null
[ "$(accepted_by build/out/selftest.mmb build/out/selftest.mm0)" = 2 ] && echo "selftest: ok" || { echo "FAIL: selftest"; fail=1; }

# The spec's relations are the functions and predicates they are read as (mm0kit/src/modes.rs):
# well-moded, and the clauses of each function pairwise exclusive. A spec with an extra clause
# for `lift` must be rejected.
echo "== lean0 modes (the spec's relations as functions)"
cargo build -q --release --bin lean0
target/release/lean0 modes > build/out/modes.txt && echo "modes: $(tail -1 build/out/modes.txt)" || { echo "FAIL: lean0 modes"; fail=1; }
{ cat build/out/lean.mm0; echo 'axiom lift_dup (n k: nat) (e: expr): $ lift n k e e $;'; } > build/out/modes-bad.mm0
if target/release/lean0 modes build/out/modes-bad.mm0 > build/out/modes-bad.txt; then echo "FAIL: lean0 modes accepted an overlapping clause"; fail=1; else echo "modes: an overlapping clause is rejected"; fi

# Each module's certificate is verified against the spec, and in TG mode against the library
# (the same proofs after the library's, audit §11).
for lean in tests/lean/*.lean; do
  echo "== ${lean#tests/lean/}"
  scripts/certify.sh --tg "$lean" > /dev/null || { echo "FAIL: $lean"; fail=1; }
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
  local edit="$1" mod="${2:-initsample}" f
  f=build/gen/$mod/$mod.mm0
  sed -e "$edit" "$f" > "build/gen/$mod/neg.mm0"
  if cmp -s "$f" "build/gen/$mod/neg.mm0"; then echo "FAIL (edit did nothing): $edit"; fail=1; return 0; fi
  if target/release/lean0 check "build/lean/$mod.ndjson" "build/gen/$mod/neg.mm0" > /dev/null; then
    echo "FAIL (accepted): $edit"; fail=1
  else echo "rejected as expected: $edit"; fi
}
stmt_neg '0,/^theorem rfl_ty/s/(srt u) (pi (bvar nz)/(srt u) (pi (bvar (s nz))/'
stmt_neg 's/^def rfl (u: lvl): expr = \$ lam (srt u) (lam (bvar nz)/def rfl (u: lvl): expr = $ lam (srt u) (lam (bvar (s nz))/'
stmt_neg '/^theorem Eq_symm_ty/s/^theorem/axiom/'
stmt_neg 's/Lean definition `rfl`/Lean definition `rfl2`/'
# A nested block's occurrences restore its constructors' types: `S.node : Array S → S`
# stated with the occurrence `List S` is caught.
stmt_neg '/^def S_D/s/(cons (app (ind_ty (Array_D lz) nz) (bvar nz))/(cons (app (ind_ty (List_D lz) nz) (bvar nz))/' nested
# An opaque constant is its own atom at its own levels: two constants sharing an atom would
# be definitionally equal (`eeqv_cst`), and a permuted level list another constant.
stmt_neg 's/cst Inh_atom/cst Pt_atom/' core
stmt_neg 's/cst Pt_atom (lcons a (lcons b lnil))/cst Pt_atom (lcons b (lcons a lnil))/' core
# A certificate's new terms are atoms and blocks, the sorts the TG encoding leaves open.
stmt_neg 's/^term Pt_atom: atom;/term Pt_atom: atom;\nterm extra: nat;/' core
rm -f build/gen/initsample/neg.mm0 build/gen/nested/neg.mm0

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
# The same parts in TG mode, each after the library, against the library's text and the parts'
# statements (the earlier parts' abstract definitions restated as terms).
tg_parts=0
for k in 0 1 2; do
  target/release/lean0 tg-link "$sh_out/initsample.part$k.mmb" build/tg/lean-tg-rest.mmb "$sh_out/tg$k.mmb" 2> /dev/null \
    && target/release/lean0 joined --tg $(for j in $(seq 0 $k); do echo "$sh_out/initsample.part$j.mm0"; done) > "$sh_out/tg$k.joined.mm0" \
    && [ "$(accepted_by "$sh_out/tg$k.mmb" "$sh_out/tg$k.joined.mm0")" = 2 ] && tg_parts=$((tg_parts + 1))
done
[ "$tg_parts" = 3 ] && echo "parts: ok in TG mode (3 certificates)" || { echo "FAIL: multi-part certificate in TG mode"; fail=1; }
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
mismatch build/out/core 's/theorem id_inh (u: lvl): \$ inh nil (pi (srt u) (pi (bvar nz) (bvar (s nz))))/theorem id_inh (u: lvl): $ inh nil (pi (srt u) (pi (bvar nz) (bvar nz)))/'
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
# (the inductive rules are theorems now, derived from the schema: a tampered statement with
# the original proof is rejected like any other)
for th in Eq_rec_refl_iota MyNat_rec_succ_iota MyList_rec_cons_iota Prod_eta PUnit_eta Sigma_eta \
          Prod_proj_0_mk And_proj_1_df; do
  tamper induct rejected --tamper-theorem "$th"
done
for ax in inst_proj ind_iota_eq proj_ty proj_mk quot_lift_mk lit_succ eeqv_cst; do tamper induct rejected --tamper-axiom "$ax"; done
# ... and rules they do not use are harmless, which shows the test can tell the difference.
tamper induct accepted --tamper-axiom nat_mul_lit
tamper induct accepted --tamper-axiom eta
# Nested blocks: the restore, the occurrence lookup, the auxiliary types' data and their iota.
tamper nested rejected --tamper-theorem tree_size_ex_ty
for ax in crst_cons rst_ty nst_hit_z aux_data_i spz_hit ndecl_cons; do tamper nested rejected --tamper-axiom "$ax"; done
tamper nested accepted --tamper-axiom spz_proj
# Literals: the ties, the operations' rules over their defining equations (the derived
# `_eqs` and `_lit` theorems, including the division-like operations' relations over the
# decision reflection, the fuel recursions and the well-founded fixpoint), and the
# binary-arithmetic relations.
tamper lit rejected --tamper-theorem lit_mul_big_ty
tamper lit rejected --tamper-theorem dbl_ex_ty
for th in Nat_add_eqs Nat_pred_eqs Nat_beq_eqs Nat_shiftRight_eqs Nat_div_eqs Nat_mod_eqs Nat_gcd_eqs \
          Nat_bitwise_eqs Nat_xor_eqs Nat_add_lit Nat_sub_lit0 Nat_ble_lit_gt Nat_shiftLeft_lit Nat_div_lit \
          Nat_mod_lit Nat_gcd_lit Nat_gcd_lit2 Nat_land_lit Nat_lor_lit; do
  tamper lit rejected --tamper-theorem "$th"
done
for ax in lit_zero lit_succ nat_add_lit add_eqs_i pred_eqs_i sub_eqs_i nat_mul_lit nat_pow_lit nat_beq_lit_gt \
          nat_ble_lit nat_shl_lit nat_shr_lit_z nat_shr_lit_s dec_eqs_i ite_eqs_i natle_dec_i nateq_dec_i \
          bool_dec_i div_eqs_i mod_eqs_i fix_eqs_i gcd_eqs_i bitwise_eqs_i bitop_eqs_i nat_div_lit nat_mod_lit \
          nat_gcd_lit nat_gcd_lit2 nat_land_lit nat_lor_lit nat_xor_lit \
          closed_lit bsucc_d1 badd_11 baddc_11 bmul_d1 bpow_d1 bdbl_d1 bxor_11; do
  tamper lit rejected --tamper-axiom "$ax"
done
# every rule is used by its `_lit` theorem's proof; what the module has no use for
tamper lit accepted --tamper-axiom quot_lift_mk
tamper lit accepted --tamper-axiom nst_hit_z
# Substitution (typing handles).
for ax in instDF cinst_z cinst_s; do tamper lit rejected --tamper-axiom "$ax"; done

# In TG mode: a tampered theorem of the certificate is rejected by the verifiers against the
# library's text, and a tampered axiom of the spec cannot be linked, since the library states
# the spec's own (the verifiers would reject the proofs that use it).
tamper_tg() {
  local mod="$1" opt="$2" what="$3" out="build/gen/tamper"
  rm -rf "$out"; mkdir -p "$out"
  target/release/lean0 gen "build/lean/$mod.ndjson" "$out" t "$opt" "$what" > /dev/null 2>&1 \
    || { echo "FAIL: lean0 $opt $what"; fail=1; return 0; }
  if ! target/release/lean0 tg-link "$out/t.mmb" build/tg/lean-tg-rest.mmb "$out/t.tg.mmb" > "$out/link.log" 2>&1; then
    if [ "$opt" = --tamper-axiom ] && grep -q "\`$what\` differs from the library's" "$out/link.log"; then
      echo "rejected as expected (tg-link): $mod $opt $what in TG mode"
    else echo "FAIL: tg-link: $mod $opt $what: $(cat "$out/link.log")"; fail=1; fi
    return 0
  fi
  target/release/lean0 joined --tg "$out/t.mm0" > "$out/t.tg.joined.mm0"
  if [ "$opt" = --tamper-theorem ] && [ "$(accepted_by "$out/t.tg.mmb" "$out/t.tg.joined.mm0")" = 0 ]; then
    echo "rejected as expected: $mod $opt $what in TG mode"
  else echo "FAIL (accepted): $mod $opt $what in TG mode"; fail=1; fi
}
tamper_tg core --tamper-theorem two_add_two_ty
tamper_tg induct --tamper-theorem MyNat_rec_succ_iota
tamper_tg lit --tamper-theorem Nat_div_lit
tamper_tg core --tamper-axiom beta
tamper_tg induct --tamper-axiom lift_app
rm -rf build/gen/tamper

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

echo "== negative tests: illegal inductive blocks (the schema must reject them)"
# Lean's kernel elaborates no illegal block, so each is made by one change to the export of
# tests/lean/Illegal.lean (whose blocks the schema certifies, the control), and `--unchecked`
# skips nanoda's check so that the schema alone judges it: `lean0 gen` must fail at the block,
# naming the schema. nanoda rejects every one of them too (two by not terminating).
for case in nonpositive universe elim mutual result occurrence index nested; do
  d="build/gen/illegal-$case"
  rm -rf "$d"; mkdir -p "$d"
  python3 scripts/illegal-export.py build/lean/illegal.ndjson "$d/x.ndjson" "$case"
  if target/release/lean0 gen "$d/x.ndjson" "$d" x --unchecked > "$d/log" 2>&1 || [ -e "$d/x.mmb" ]; then
    echo "FAIL: an illegal inductive block was certified: $case"; fail=1
  elif ! grep -q 'by the schema' "$d/log"; then
    echo "FAIL: not rejected by the schema: $case"; fail=1
  else
    echo "rejected as expected: $(grep -m1 'by the schema' "$d/log" | sed 's/^lean0: //; s/: horn:.*//') ($case)"
  fi
done

[ "$fail" = 0 ] && echo "all tests passed" || { echo "SOME TESTS FAILED"; exit 1; }
