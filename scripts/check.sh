#!/usr/bin/env bash
# Compile an .mm0/.auf pair with Aufbau's abc and verify the result with both
# mm0-zig and mm0-c. Usage: scripts/check.sh FILE.mm0 FILE.auf [OUT.mmb]
# Tools: ABC, MM0_ZIG, MM0_C env vars, by default abc, mm0-zig and mm0-c from PATH (the dev
# shell has this flake's pinned ones).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
mm0="$1"; auf="$2"
out="${3:-$root/build/out/$(basename "${mm0%.mm0}").mmb}"
ABC="${ABC:-abc}"
MM0_ZIG="${MM0_ZIG:-mm0-zig}"
MM0_C="${MM0_C:-mm0-c}"
mkdir -p "$(dirname "$out")"
joined="${out%.mmb}.joined.mm0"
"$ABC" compile "$mm0" "$auf" "$out"
"$ABC" join "$mm0" > "$joined"
"$MM0_ZIG" "$out" < "$joined" > /dev/null && echo "mm0-zig: ok ($out)"
"$MM0_C" "$out" < "$joined" && echo "mm0-c:   ok"
