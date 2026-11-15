#!/usr/bin/env bash
# Staged exact-head check for the Track 1 selected-owner assembly.
# Requires the pinned local Lean/Lake workspace. Not a full Track 1 proof.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LEAN_NUM_THREADS:=1}"
export LEAN_NUM_THREADS
echo "Git head: $(git rev-parse HEAD)"
echo "Toolchain: $(cat lean-toolchain)"
log="${1:-/tmp/track1-selected-assembly-axioms.log}"
lake build \
  Girth.Track1FullSelectedOrderedLifts \
  Girth.Track1FullSelectedSupportPieces \
  Girth.Track1ActualSelectedOwnerColourArrow \
  Girth.Track1OwnerSplitFinite \
  Girth.Track1OrderedPhysicalOwners
lake env lean CheckTrack1SelectedAssembly.lean > "$log" 2>&1
cat "$log"
python3 scripts/check_axioms.py "$log" CheckTrack1SelectedAssembly.lean
echo "Conditional selected-assembly proofs passed the strict focused gate."
echo "The original EHN selected-family and m=3 picture/fusion assembly still need integration."
