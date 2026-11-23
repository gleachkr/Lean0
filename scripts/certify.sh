#!/usr/bin/env bash
# Certify a Lean module end to end: compile it, export it with lean4export, generate the
# certificate with `lean0 gen`, verify it with mm0-zig and mm0-c against the text `lean0 joined`
# builds, and check its statements against the export with `lean0 check`.
# Usage: scripts/certify.sh [--tg] MODULE.lean [OUT_DIR]   (default OUT_DIR: build/gen/<module>)
# With --tg it also verifies the certificate in TG mode (audit §11): `lean0 tg-link` puts it
# after the TG library's MMB file (TG_LIB, by default build/tg/lean-tg-rest.mmb, which
# scripts/tg-check.sh spec/tg/lean-tg-rest.mm0 makes), and both verifiers check the result
# against `lean0 joined --tg`.
# The module is compiled with Lean v4.35.0 (lean4export's toolchain) in build/lean/. Tools:
# LEAN4EXPORT, MM0_ZIG, MM0_C env vars, by default lean4export, mm0-zig and mm0-c from PATH
# (lean4export at the revision lean0 uses; scripts/test.sh builds one in tests/lake).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
tg=; if [ "${1:-}" = --tg ]; then tg=1; shift; fi
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
# lean4export finds Lean's own .olean files through `lean`, so the export is pinned to the same
# toolchain as the compilation (elan's default may be a later Lean, whose files it cannot read).
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-leanprover/lean4:v4.35.0}"
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
if [ -n "$tg" ]; then
  "$lean0" tg-link "$out/$name.mmb" "${TG_LIB:-$root/build/tg/lean-tg-rest.mmb}" "$out/$name.tg.mmb"
  "$lean0" joined --tg "$out/$name.mm0" > "$out/$name.tg.joined.mm0"
  "$MM0_ZIG" "$out/$name.tg.mmb" < "$out/$name.tg.joined.mm0" > /dev/null && echo "mm0-zig: ok in TG mode ($out/$name.tg.mmb)"
  "$MM0_C" "$out/$name.tg.mmb" < "$out/$name.tg.joined.mm0" && echo "mm0-c:   ok in TG mode"
fi
# the statements say what the export's declarations say
"$lean0" check "$work/$name.ndjson" "$out/$name.mm0" | tail -1
