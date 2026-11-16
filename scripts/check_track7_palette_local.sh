#!/usr/bin/env bash
# Focused local check for the clean Track 7 palette/type and RR-tail interface.
# Requires the repository-pinned Lean + Lake + mathlib workspace already present.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lake build Girth.TrainRecursiveUnrestrictedOrderInterface

checks=(
  CheckTrainRecursiveUniformAllColours
  CheckTrainRecursiveUniformAllInputs
  CheckTrainRecursiveCutoffTwoPartObstruction
  CheckTrainRecursiveUnrestrictedOrderInterface
)
for check in "${checks[@]}"; do
  LOG="$(mktemp "${TMPDIR:-/tmp}/track7-palette-axioms.XXXXXXXX.log")"
  lake env lean "${check}.lean" | tee "$LOG"
  python3 scripts/check_axioms.py "$LOG" "${check}.lean"
  rm -f "$LOG"
done
