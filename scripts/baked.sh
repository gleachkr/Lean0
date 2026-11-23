#!/usr/bin/env bash
# scripts/baked.sh [--check]: lean0/baked/baked.ndjson from lean0/baked/Baked.lean (the proofs
# lean0 carries for the division-like literal operations, audit §5). Compiles the file with
# Lean v4.35.0, exports its theorems and what the operations themselves depend on with
# lean4export (LEAN4EXPORT, default: from PATH), and keeps what the theorems need beyond that
# (scripts/baked.py). With --check, compares with the file in the repository instead of
# writing it.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
EXPORT="${LEAN4EXPORT:-lean4export}"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-leanprover/lean4:v4.35.0}"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
cp "$root/lean0/baked/Baked.lean" "$work/"
cd "$work"
lean -o Baked.olean Baked.lean
# each group: the theorems (and stand-in definitions) one relation's proof takes, and the
# operations it may assume declared
DIV="Lean0.d_div_add_mod,Lean0.c_mod_lt,Lean0.d_div_zero,Lean0.mul,Lean0.mod"
MOD="Lean0.m_div_add_mod,Lean0.mod_lt,Lean0.c_div_zero,Lean0.mul,Lean0.div"
GCD="Lean0.gcd_zero,Lean0.gcd_succ"
BIT="Lean0.div_add_mod,Lean0.mod_lt,Lean0.d_div_zero,Lean0.mul,Lean0.land_rec,Lean0.lor_rec,Lean0.xor_rec"
ALL="$DIV,$MOD,$GCD,$BIT"
LEAN_PATH="$work" "$EXPORT" Baked -- ${ALL//,/ } > all.ndjson
LEAN_PATH="$work" "$EXPORT" Baked -- Nat.div Nat.le Eq > div.ndjson
LEAN_PATH="$work" "$EXPORT" Baked -- Nat.mod Nat.le Eq > mod.ndjson
LEAN_PATH="$work" "$EXPORT" Baked -- Nat.gcd Nat.le Eq > gcd.ndjson
LEAN_PATH="$work" "$EXPORT" Baked -- Nat.land Nat.lor Nat.xor Nat.le Eq > bit.ndjson
python3 -I "$root/scripts/baked.py" all.ndjson baked.ndjson "$DIV=div.ndjson" "$MOD=mod.ndjson" "$GCD=gcd.ndjson" "$BIT=bit.ndjson"
if [ "${1:-}" = "--check" ]; then
  cmp baked.ndjson "$root/lean0/baked/baked.ndjson" || { echo "baked: lean0/baked/baked.ndjson is not what Baked.lean gives (run scripts/baked.sh)" >&2; exit 1; }
else
  cp baked.ndjson "$root/lean0/baked/baked.ndjson"
fi
