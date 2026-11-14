#!/usr/bin/env bash
# Exact-head local gate for the numbered Track 7 selected lower-step module.
# Run from any directory after restoring the repository-pinned Lean/mathlib cache.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

# Build the real lemma and its transitive imports before invoking #print axioms.
lake build Girth.TrainRecursiveActualLowerRefiningStep

LOG="$(mktemp "${TMPDIR:-/tmp}/track7-axioms.XXXXXXXX.log")"
trap 'rm -f "$LOG"' EXIT
lake env lean CheckTrainRecursiveActualLowerRefiningStep.lean | tee "$LOG"
python3 scripts/check_axioms.py "$LOG" CheckTrainRecursiveActualLowerRefiningStep.lean
