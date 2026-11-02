#!/usr/bin/env bash
# Clone reference projects into refs/ (untracked): reading material for development (Lean4Lean,
# the MM0 sources, lean4export, Aufbau, papers). Nothing builds from it; scripts/nanoda.sh uses
# refs/nanoda_lib when it has the pinned commit and downloads it otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p refs/papers
for r in ammkrn/nanoda_lib digama0/lean4lean digama0/mm0 leanprover/lean4export \
         gleachkr/Aufbau gleachkr/aufbau-syntax; do
  d="refs/${r#*/}"
  [ -d "$d" ] || git clone --depth 50 "https://github.com/$r.git" "$d"
done
[ -f refs/papers/lean4lean-arxiv.pdf ] || curl -sL -o refs/papers/lean4lean-arxiv.pdf https://arxiv.org/pdf/2403.14064
[ -f refs/papers/types2025-lean4lean-slides.pdf ] || curl -sL -o refs/papers/types2025-lean4lean-slides.pdf \
  https://msp-strath.github.io/MSPweb/types2025/slides/TYPES2025-slides31.pdf
