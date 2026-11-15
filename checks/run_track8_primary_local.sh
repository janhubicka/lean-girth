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
  Girth.FiniteTraceSimplicialCriterion \
  Girth.FiniteTracePEORank \
  2>&1 | tee "$log_dir/build.log"

echo "Running focused #check / #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8Primary.lean 2>&1 | tee "$log_dir/primary.log"

echo "Running exhaustive dependency #print axioms gate"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean \
  CheckTrack8AllDependencies.lean 2>&1 | tee "$log_dir/all-dependencies.log"

if grep -E -q 'sorryAx|Lean\.sorry|admit' \
    "$log_dir/primary.log" "$log_dir/all-dependencies.log"; then
  echo "ERROR: unexpected proof-hole axiom in Track 8 checks" >&2
  exit 1
fi

echo "WARNING: inspect every printed transitive axiom, not only the hole grep."
echo "Track 8 local build/check completed. Logs: $log_dir"
