#!/usr/bin/env bash
# Exact-head focused kernel gate for the actual Track 1 selected EHN assembly.
# Requires the pinned Lean toolchain and complete Lake dependency graph.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "HEAD: $(git rev-parse HEAD)"
echo "TOOLCHAIN: $(cat lean-toolchain)"
export LEAN_NUM_THREADS=1
source_count=$(grep -c '^#print axioms ' CheckTrack1ActualPartite.lean)
test "$source_count" -eq 17 || {
  echo "Wrong actual-partite Track 1 axiom inventory: $source_count" >&2
  exit 1
}
if grep -nE '^[[:space:]]*(sorry|admit|axiom)[[:space:]]' \
    Girth/Track1ActualSelectedLiftPairwiseAllowed.lean \
    Girth/Track1ColourFromRel.lean \
    Girth/Track1ControlledPhysicalIntersection.lean \
    Girth/Track1EHNColouredPresentation.lean \
    Girth/Track1EHNIndexedSelected.lean \
    Girth/Track1ForbiddenPartDegreeOne.lean \
    Girth/Track1FullSelectedWitnessEmbeddings.lean \
    Girth/Track1OldSelectedColouredPresentation.lean \
    Girth/Track1PhysicalActualSelectedIntersections.lean \
    Girth/Track1PhysicalSelectedRepresentatives.lean \
    Girth/Track1PhysicalFamilyActualMixedLF2.lean \
    Girth/Track1TriangleFreePhysicalFamily.lean; then
  echo "Explicit proof placeholder detected" >&2
  exit 1
fi
lake build \
  Girth.Track1FullSelectedWitnessEmbeddings \
  Girth.Track1PhysicalActualSelectedIntersections \
  Girth.Track1EHNIndexedSelected \
  Girth.Track1PhysicalFamilyActualMixedLF2 \
  Girth.Track1TriangleFreePhysicalFamily
log="${1:-/tmp/check-track1-actual-partite-axioms.log}"
lake env lean CheckTrack1ActualPartite.lean > "$log" 2>&1
cat "$log"
python3 scripts/check_axioms.py "$log" CheckTrack1ActualPartite.lean
echo "Exact selected EHN and LF2 adapters checked; full partite/fusion is still open."
