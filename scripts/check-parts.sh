#!/usr/bin/env bash
# scripts/check-parts.sh [--follow] [--delete] [--export FILE] OUT NAME: check a multi-part certificate
# (`lean0 gen ... --parts P`): OUT/NAME.part0.{mm0,mmb}, NAME.part1.*, ...
#
# Part K is verified, with both verifiers, against the text `lean0 joined` builds from the
# statement files of parts 0..K: the spec, the earlier parts' statements restated (theorems as
# axioms, abstract defs as terms), then part K's own statements. So the axioms a part assumes are
# exactly the theorems the earlier parts prove (audit §7). JOBS (default 4) parts at a time.
#
# --follow: check the parts while lean0 is still making them, in order, waiting for each
# (lean0 writes NAME.parts with their number, and NAME.partK.failed for one that failed).
# --delete: delete each part's .mmb once both verifiers have run on it, whether they accept it
# or not, so that a large certificate never has to be on disk all at once (with `lean0 gen
# --max-pending M`, which waits for the deletions). The results go to NAME.check.log; a
# rejected part can be made again on its own with `lean0 gen ... --shard LO HI --part K` (the
# part boundaries are in lean0's output).
# --export FILE: also check that the statements say what the export's declarations say
# (`lean0 check` over all parts' statements).
# Tools: LEAN0, MM0_ZIG, MM0_C env vars, by default target/release/lean0, and mm0-zig and mm0-c
# from PATH (the dev shell has this flake's pinned ones).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
follow=0 delete=0 export=""
while [ $# -gt 2 ]; do
  case "$1" in
    --follow) follow=1 ;;
    --delete) delete=1 ;;
    --export) export="$2"; shift ;;
    *) echo "usage: check-parts.sh [--follow] [--delete] [--export FILE] OUT NAME" >&2; exit 2 ;;
  esac
  shift
done
out="$1" name="$2"
LEAN0="${LEAN0:-$root/target/release/lean0}"
MM0_ZIG="${MM0_ZIG:-mm0-zig}"
MM0_C="${MM0_C:-mm0-c}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
log="$out/$name.check.log"
: > "$log"

if [ "$follow" = 1 ]; then
  until [ -f "$out/$name.parts" ]; do sleep 5; done
  total="$(cat "$out/$name.parts")"
else
  total=0
  while [ -f "$out/$name.part$total.mmb" ]; do total=$((total + 1)); done
  [ "$total" -gt 0 ] || { echo "FAIL: no parts $out/$name.part*.mmb"; exit 1; }
fi

# verify K: both verifiers on part K against the text built for it, one line in the log
verify() {
  local k="$1" part="$out/$name.part$1" r=""
  "$MM0_ZIG" "$part.mmb" < "$tmp/joined$k" > /dev/null 2>&1 || r="$r mm0-zig"
  "$MM0_C" "$part.mmb" < "$tmp/joined$k" > /dev/null 2>&1 || r="$r mm0-c"
  local size; size="$(stat -c %s "$part.mmb")"
  if [ -z "$r" ]; then
    echo "ok: part $k ($size bytes)" >> "$log"
  else
    local note=""
    [ "$size" -gt 4294967295 ] && note=", over mm0-zig's 4 GiB"
    echo "FAIL (${r# } rejects): part $k ($size bytes$note)" >> "$log"
  fi
  [ "$delete" = 0 ] || rm -f "$part.mmb"
  rm -f "$tmp/joined$k"
}

stmts=()
fail=0
for k in $(seq 0 $((total - 1))); do
  part="$out/$name.part$k"
  until [ -f "$part.mmb" ]; do
    if [ -f "$part.failed" ] || [ "$follow" = 0 ]; then echo "FAIL: part $k is missing" | tee -a "$log"; exit 1; fi
    sleep 5
  done
  stmts+=("$part.mm0")
  if ! "$LEAN0" joined "${stmts[@]}" > "$tmp/joined$k" 2>> "$log"; then
    echo "FAIL: part $k: no text to verify against" | tee -a "$log"; exit 1
  fi
  while [ "$(jobs -rp | wc -l)" -ge "${JOBS:-4}" ]; do wait -n || true; done
  verify "$k" &
done
wait
sort -V -k3 "$log"
grep -q '^FAIL' "$log" && fail=1
if [ -n "$export" ]; then
  "$LEAN0" check "$export" "${stmts[@]}" | tail -1 | tee -a "$log"
  [ "${PIPESTATUS[0]}" = 0 ] || fail=1
fi
[ "$fail" = 0 ] && echo "all $total parts: ok" || exit 1
