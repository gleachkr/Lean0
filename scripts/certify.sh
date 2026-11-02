#!/usr/bin/env bash
# Certify a Lean module end to end: compile it, export it with lean4export, generate the
# certificate with `lean0 gen`, verify it with mm0-zig and mm0-c against the text `lean0 joined`
# builds, and check its statements against the export with `lean0 check`.
# Usage: scripts/certify.sh MODULE.lean [OUT_DIR]   (default OUT_DIR: build/gen/<module>)
# The module is compiled with Lean v4.35.0 (lean4export's toolchain) in build/lean/. Tools:
# LEAN4EXPORT, MM0_ZIG, MM0_C env vars, by default lean4export, mm0-zig and mm0-c from PATH
# (lean4export at the revision lean0 uses; scripts/test.sh builds one in tests/lake).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
src="$(realpath "$1")"
mod="$(basename "${src%.lean}")"
name="$(echo "$mod" | tr '[:upper:]' '[:lower:]')"
out="${2:-$root/build/gen/$name}"
EXPORT="${LEAN4EXPORT:-lean4export}"
MM0_ZIG="${MM0_ZIG:-mm0-zig}"
MM0_C="${MM0_C:-mm0-c}"
work="$root/build/lean"
mkdir -p "$work" "$out"
cp "$src" "$work/$mod.lean"
(cd "$work" && lean +leanprover/lean4:v4.35.0 -o "$mod.olean" "$mod.lean") || { echo "certify: lean failed on $src" >&2; exit 1; }
# A `-- lean0-export: NAME...` line restricts the export to those declarations and their dependencies.
names="$(sed -n 's/^-- lean0-export://p' "$src" | head -1)"
if [ -n "$names" ]; then
  (cd "$work" && LEAN_PATH="$work" "$EXPORT" "$mod" -- $names > "$name.ndjson")
else
  (cd "$work" && LEAN_PATH="$work" "$EXPORT" "$mod" > "$name.ndjson")
fi
"$root/scripts/nanoda.sh" apply > /dev/null
cargo build -q --release --manifest-path "$root/Cargo.toml" --bin lean0
lean0="$root/target/release/lean0"
"$lean0" gen "$work/$name.ndjson" "$out" "$name"
# the text to verify against: the spec and the statements, built by the trusted side
"$lean0" joined "$out/$name.mm0" > "$out/$name.joined.mm0"
"$MM0_ZIG" "$out/$name.mmb" < "$out/$name.joined.mm0" > /dev/null && echo "mm0-zig: ok ($out/$name.mmb)"
"$MM0_C" "$out/$name.mmb" < "$out/$name.joined.mm0" && echo "mm0-c:   ok"
# the statements say what the export's declarations say
"$lean0" check "$work/$name.ndjson" "$out/$name.mm0" | tail -1
