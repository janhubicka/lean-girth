#!/usr/bin/env bash
# Focused Lean gate for the changing-coloured-edge-arity rank interface.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake build Girth.TrainRecursiveUniformLanguages
LOG="$(mktemp "${TMPDIR:-/tmp}/track7-language-axioms.XXXXXXXX.log")"
trap 'rm -f "$LOG"' EXIT
lake env lean CheckTrainRecursiveUniformLanguages.lean | tee "$LOG"
python3 scripts/check_axioms.py "$LOG" CheckTrainRecursiveUniformLanguages.lean
