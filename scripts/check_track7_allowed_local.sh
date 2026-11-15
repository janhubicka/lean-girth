#!/usr/bin/env bash
# Focused Track 7 permitted-part compatibility check (rootless / no network).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lake build Girth.TrainRecursiveGlobalAllowedCompatibility
LOG="$(mktemp "${TMPDIR:-/tmp}/track7-global-allowed.XXXXXXXX.log")"
trap 'rm -f "$LOG"' EXIT
lake env lean CheckTrainRecursiveGlobalAllowedCompatibility.lean | tee "$LOG"
python3 scripts/check_axioms.py "$LOG" CheckTrainRecursiveGlobalAllowedCompatibility.lean
