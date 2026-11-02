#!/usr/bin/env bash
# scripts/nanoda.sh apply [--force] | diff: lean0 builds against nanoda_lib
# (https://github.com/ammkrn/nanoda_lib) at a pinned commit plus Lean0's patch,
# patches/nanoda_lib.patch, in build/nanoda (not tracked). flake.nix applies the same patch to
# the same commit; keep REV in step with it.
#
# - apply: (re)make build/nanoda as upstream at REV plus the patch, unless it is already that.
#   It refuses to discard edits made in build/nanoda since (`--force` discards them).
# - diff: after editing build/nanoda, write its changes against upstream to the patch.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
REV=d0a02cc5defadd683f62f9d078f41688314fa31f   # v0.4.30
PATCH=patches/nanoda_lib.patch
DIR=build/nanoda
STAMP=build/nanoda.applied   # the patch build/nanoda was made from
FILES="Cargo.toml Cargo.lock LICENSE README.md rustfmt.toml src"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# upstream DIR: nanoda_lib at REV (its sources, not its test resources) in DIR
upstream() {
  mkdir -p "$1"
  if git -C refs/nanoda_lib cat-file -e "$REV^{commit}" 2>/dev/null; then
    git -C refs/nanoda_lib archive "$REV" -- $FILES | tar -x -C "$1"
  else
    curl -sfL "https://github.com/ammkrn/nanoda_lib/archive/$REV.tar.gz" | tar -xz -C "$1" --strip-components=1
    local keep=""
    for f in $FILES; do keep="$keep ! -name $f"; done
    find "$1" -mindepth 1 -maxdepth 1 $keep -exec rm -rf {} +
  fi
}

# The patch that makes upstream into build/nanoda: a header, then `diff -ruN` without timestamps.
patch_text() {
  rm -rf "$tmp/a" "$tmp/b"
  upstream "$tmp/a"
  cp -r "$DIR" "$tmp/b"
  cat <<EOF
Lean0's changes to nanoda_lib (https://github.com/ammkrn/nanoda_lib) at commit
$REV (v0.4.30),
applied by scripts/nanoda.sh (into build/nanoda) and by flake.nix. There are two kinds:
the tracing hook (src/trace.rs, the recording calls in src/tc.rs and three cache fields in
src/util.rs), and making public the items the lean0 crates use. After editing build/nanoda,
regenerate this file with \`scripts/nanoda.sh diff\`.

EOF
  (cd "$tmp" && diff -ruN a b || [ $? = 1 ]) | sed -E 's/^((---|\+\+\+) [^\t]*)\t.*/\1/'
}

case "${1:-}" in
  apply)
    if [ -d "$DIR" ]; then
      patch_text > "$tmp/now"
      if cmp -s "$tmp/now" "$STAMP" 2>/dev/null; then
        # no edits: done if it was made from this patch
        cmp -s "$STAMP" "$PATCH" && exit 0
      elif [ "${2:-}" != --force ]; then
        echo "nanoda.sh: $DIR has edits not in $PATCH (\`scripts/nanoda.sh diff\` saves them, \`apply --force\` discards them)" >&2
        exit 1
      fi
    fi
    rm -rf "$DIR" "$STAMP"
    upstream "$DIR"
    patch -s -p1 -d "$DIR" < "$PATCH"
    cp "$PATCH" "$STAMP"
    echo "nanoda.sh: $DIR is nanoda_lib ${REV:0:7} with $PATCH"
    ;;
  diff)
    [ -d "$DIR" ] || { echo "nanoda.sh: no $DIR (run \`scripts/nanoda.sh apply\`)" >&2; exit 1; }
    patch_text > "$tmp/now"
    cp "$tmp/now" "$PATCH"
    cp "$tmp/now" "$STAMP"
    echo "nanoda.sh: wrote $PATCH"
    ;;
  *) echo "usage: scripts/nanoda.sh apply [--force] | diff" >&2; exit 2 ;;
esac
