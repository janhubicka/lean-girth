#!/usr/bin/env bash
# Build exact heads of the selected-coloured-witness assembly, then inspect axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
echo "HEAD: $(git rev-parse HEAD)"
echo "Lean toolchain: $(cat lean-toolchain)"
test "$(grep -c '^#print axioms ' CheckTrack1ColouredSelectedWitness.lean)" -eq 10
if grep -nE '^[[:space:]]*(sorry|admit|axiom)[[:space:]]' \
  Girth/Track1ActualSelectedCoverage.lean \
  Girth/Track1ActualSelectedBStrong.lean \
  Girth/Track1SplitSelectedMixedLF2.lean \
  Girth/Track1ColouredSelectedWitnessAssembly.lean; then
  echo "ERROR: explicit placeholder in selected-witness source" >&2
  exit 1
fi
lake build Girth.Track1ColouredSelectedWitnessAssembly
log="${1:-/tmp/track1-coloured-witness-axioms.log}"
lake env lean CheckTrack1ColouredSelectedWitness.lean > "$log" 2>&1
cat "$log"
python3 scripts/check_axioms.py "$log" CheckTrack1ColouredSelectedWitness.lean
echo "Only conditional selected-witness components certified. Partite fusion remains OPEN."
