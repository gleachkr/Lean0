#!/usr/bin/env bash
# Compile and verify the TG library (spec/tg): abc compiles spec/tg/all.mm0
# (or the file given) with the proofs beside each imported theory file, then
# both verifiers check the joined text. Tools from the dev shell (`nix develop`);
# ABC, MM0_ZIG and MM0_C override them. Theorems admitted with `sorry!` are
# allowed through (every tool exits 3 for them) and counted at the end.
set -uo pipefail
cd "$(dirname "$0")/.."
ABC=${ABC:-abc}; MM0_ZIG=${MM0_ZIG:-mm0-zig}; MM0_C=${MM0_C:-mm0-c}
top=${1:-spec/tg/all.mm0}
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
echo "tg-check: $top verified ($(grep -c '^theorem' "$out/$name.joined.mm0") theorems, $(grep -c '^axiom' "$out/$name.joined.mm0") axioms; $admitted admitted with sorry!)"
