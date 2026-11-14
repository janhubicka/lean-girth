#!/usr/bin/env bash
# Local exact-head gate for the stacked Track 7 universal lower-rank induction.
# Requires repository-pinned Lean/mathlib already installed (no network calls).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lake build Girth.TrainRecursiveUniformOperators
LOG="$(mktemp "${TMPDIR:-/tmp}/track7-rank-axioms.XXXXXXXX.log")"
trap 'rm -f "$LOG"' EXIT
lake env lean CheckTrainRecursiveUniformLowerRank.lean | tee "$LOG"
python3 scripts/check_axioms.py "$LOG" CheckTrainRecursiveUniformLowerRank.lean
