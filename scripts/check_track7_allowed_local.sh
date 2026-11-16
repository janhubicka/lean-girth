#!/usr/bin/env bash
# Focused Track 7 permitted-part compatibility and stage-retyping gate.
# Requires the pinned Lean/mathlib workspace locally; no network calls.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lake build Girth.TrainRecursiveAllowedMonotone
for check in CheckTrainRecursiveGlobalAllowedCompatibility CheckTrainRecursiveAllowedMonotone; do
  LOG="$(mktemp "${TMPDIR:-/tmp}/track7-global-allowed.XXXXXXXX.log")"
  trap 'rm -f "$LOG"' EXIT
  lake env lean "${check}.lean" | tee "$LOG"
  python3 scripts/check_axioms.py "$LOG" "${check}.lean"
  rm -f "$LOG"
done
