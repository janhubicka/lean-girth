#!/usr/bin/env bash
# Numbered Track 2: exact-head, strict-axiom LOCAL validation gate.
# This uses the repository's pinned toolchain and existing axiom parser.
# It does NOT update dependencies, start Actions, or claim success before Lean runs.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

if ! command -v lake >/dev/null 2>&1; then
  echo "Track 2 requires the pinned Lean/Lake installation; 'lake' was not found." >&2
  exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "Track 2 requires Python 3 for the repository's strict axiom checker." >&2
  exit 2
fi

echo "Track 2 exact checkout: $(git rev-parse HEAD)"
echo "Pinned toolchain: $(cat lean-toolchain)"
echo "Building independent modules in dependency order."
modules=(
  Girth.ForestSeparatorCrossAllowed
  Girth.ForestBinarySeparatorLift
  Girth.ForestGeneralJoinLift
  Girth.ForestDuplicateLabelNormalization
  Girth.ForestDuplicateLabelGeometry
  Girth.ForestRetainedSetLift
  Girth.ForestTraceAcyclic
  Girth.ForestActiveTraceGirth
  Girth.ForestCompletionTraceBridge
  Girth.ForestActiveTraceBoundary
  Girth.ForestOldActiveGirth
  Girth.ForestFiniteSetCompletion
  Girth.ForestCopySetCompletion
  Girth.ForestOldActiveSetGirth
  Girth.ForestTwoMemberLinearity
  Girth.ForestDirectIncrementLinearity
  Girth.CheckTrack2Trace
)
for module in "${modules[@]}"; do
  echo "== lake build $module =="
  lake build "$module"
done

LOG="$(mktemp "${TMPDIR:-/tmp}/track2-axioms.XXXXXXXX.log")"
trap 'rm -f "$LOG"' EXIT

lake env lean Girth/CheckTrack2Trace.lean | tee "$LOG"
python3 scripts/check_axioms.py "$LOG" Girth/CheckTrack2Trace.lean

echo "Track 2 kernel gate passed for $(git rev-parse HEAD)."
