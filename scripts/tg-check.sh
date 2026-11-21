#!/usr/bin/env bash
# Compile and verify the TG library (spec/tg): abc compiles the chain's top,
# spec/tg/lean-tg-rest.mm0 (or the file given), with the proofs beside each
# imported theory file, then both verifiers check the joined text. Tools from the
# dev shell (`nix develop`); ABC, MM0_ZIG and MM0_C override them. Theorems
# admitted with `sorry!` are allowed through (every tool exits 3 for them) and
# counted at the end; abc's other warnings are printed and counted too.
set -uo pipefail
# A proof that no longer fits its statements can make abc use all memory (the check needs about
# 4 GB): cap the address space, in kB (TG_MEM_KB).
ulimit -v "${TG_MEM_KB:-20000000}"
cd "$(dirname "$0")/.."
ABC=${ABC:-abc}; MM0_ZIG=${MM0_ZIG:-mm0-zig}; MM0_C=${MM0_C:-mm0-c}
top=${1:-spec/tg/lean-tg-rest.mm0}
out=build/tg; mkdir -p "$out"
name=$(basename "${top%.mm0}")
auf="${top%.mm0}.auf"; [ -f "$auf" ] || auf=/dev/null
run() { "$@"; local st=$?; [ $st -eq 0 ] || [ $st -eq 3 ] || return $st; }
run "$ABC" compile "$top" "$auf" "$out/$name.mmb" 2> "$out/$name.compile.log" \
  || { cat "$out/$name.compile.log"; exit 1; }
"$ABC" join "$top" > "$out/$name.joined.mm0" || exit 1
run "$MM0_ZIG" "$out/$name.mmb" < "$out/$name.joined.mm0" > "$out/$name.zig.log" 2>&1
run "$MM0_C" "$out/$name.mmb" < "$out/$name.joined.mm0" > "$out/$name.c.log" 2>&1
admitted=$(grep -c "uses sorry$" "$out/$name.c.log" || true)
# Each warning is a block from its `warning:` line to the next one. abc prints
# a limited number and then says how many it omitted, of either kind.
awk '/^(warning|error):/ { show = ($0 !~ /admitted with sorry!|additional warning/) } show' \
  "$out/$name.compile.log" > "$out/$name.warnings.log"
warnings=$(grep -c '^warning:' "$out/$name.warnings.log" || true)
omitted=$(sed -n 's/^warning: omitted \([0-9]*\) additional warning.*/\1/p' "$out/$name.compile.log")
cat "$out/$name.warnings.log" >&2
[ -n "$omitted" ] && warnings="$warnings warnings, $omitted more not shown" || warnings="$warnings warnings"
echo "tg-check: $top verified ($(grep -c '^theorem' "$out/$name.joined.mm0") theorems, $(grep -c '^axiom' "$out/$name.joined.mm0") axioms; $admitted admitted with sorry!; $warnings)"
