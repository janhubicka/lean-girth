#!/usr/bin/env bash
# Exact-head Track 8 LOCAL Lean gate, no GitHub Actions or network assumed.
# Usage: bash checks/run_track8_primary_local.sh [log-directory]
set -euo pipefail

log_dir="${1:-/tmp/lean-girth-track8-audit}"
mkdir -p "$log_dir"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: pinned Lean/Lake toolchain unavailable; no validation performed" >&2
  exit 2
fi

echo "Track 8 source revision: $(git rev-parse HEAD)"
echo "Building primary trace and cycle proof modules"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build \
  Girth.FiniteTracePEOCount \
  Girth.FiniteTraceFinRotateCycle \
  Girth.FiniteTraceTriangleCycle \
  Girth.FiniteTraceCycleCertificate \
  Girth.FiniteTraceCycleGraphFacts \
  Girth.FiniteTraceChordalEndpoint \
  Girth.FiniteTraceSimplicialCriterion \
  Girth.FiniteTracePEORank \
  Girth.FiniteTraceOrderReduct Girth.OrderReductUniformEdge \
  2>&1 | tee "$log_dir/build.log"

echo "Running focused #check / #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8Primary.lean 2>&1 | tee "$log_dir/primary.log"

echo "Running exhaustive dependency #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8AllDependencies.lean 2>&1 | tee "$log_dir/all-dependencies.log"

echo "Running actual picture extraction #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8PictureExtraction.lean 2>&1 | tee "$log_dir/picture-extraction.log"

echo "Running the order reduct #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8OrderReduct.lean 2>&1 | tee "$log_dir/order-reduct.log"

echo "Running the uniform-edge carrier-colouring #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8UniformEdgeArrow.lean 2>&1 | tee "$log_dir/uniform-edge-arrow.log"

python3 scripts/check_axioms.py "$log_dir/primary.log" CheckTrack8Primary.lean
python3 scripts/check_axioms.py "$log_dir/all-dependencies.log" CheckTrack8AllDependencies.lean
python3 scripts/check_axioms.py "$log_dir/picture-extraction.log" CheckTrack8PictureExtraction.lean
python3 scripts/check_axioms.py "$log_dir/order-reduct.log" CheckTrack8OrderReduct.lean
python3 scripts/check_axioms.py "$log_dir/uniform-edge-arrow.log" CheckTrack8UniformEdgeArrow.lean
echo "Track 8 local build/check completed. Logs: $log_dir"
