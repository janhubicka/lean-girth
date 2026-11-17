#!/usr/bin/env bash
# Numbered Track 2: local Lean and strict axiom gates.
# Run: bash scripts/check_track2_local.sh [all|active|increment|join|physical]
# No explicit dependency update or GitHub Actions job is started.
# Restore the pinned local cache first: Lake may fetch missing packages.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

if ! command -v lake >/dev/null 2>&1; then
  echo "Track 2 requires locally installed Lean/Lake ('lake' missing)." >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "Track 2 requires Python 3 to run scripts/check_axioms.py." >&2
  exit 2
fi

mode="${1:-all}"
case "$mode" in
  all|active|increment|join|physical) ;;
  *) echo "Usage: $0 [all|active|increment|join|physical]" >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  echo "Usage: $0 [all|active|increment|join|physical]" >&2
  exit 2
fi

echo "Track 2 checkout: $(git rev-parse HEAD)"
echo "Pinned toolchain: $(cat lean-toolchain)"
if [[ -n "$(git status --porcelain)" ]]; then
  echo "WARNING: worktree is dirty; record the exact local changes in any certificate." >&2
fi

failures=0
passes=0
run_gate() {
  local label="$1" module="$2" file="$3"
  local log
  echo "=== Track 2: $label (lake build $module) ==="
  if ! lake build "$module"; then
    echo "FAILED: building $module" >&2
    failures=$((failures + 1))
    return
  fi
  log="$(mktemp "${TMPDIR:-/tmp}/track2-axioms.XXXXXXXX.log")"
  if ! lake env lean "$file" > "$log" 2>&1; then
    cat "$log"
    rm -f "$log"
    echo "FAILED: elaborating $file" >&2
    failures=$((failures + 1))
    return
  fi
  cat "$log"
  if python3 scripts/check_axioms.py "$log" "$file"; then
    passes=$((passes + 1))
    echo "PASSED: $label"
  else
    failures=$((failures + 1))
    echo "FAILED: strict axiom audit of $file" >&2
  fi
  rm -f "$log"
}

if [[ "$mode" == all || "$mode" == active ]]; then
  run_gate active Girth.CheckTrack2ActiveGirth Girth/CheckTrack2ActiveGirth.lean
fi
if [[ "$mode" == all || "$mode" == increment ]]; then
  run_gate increment Girth.CheckTrack2DirectIncrement Girth/CheckTrack2DirectIncrement.lean
fi
if [[ "$mode" == all || "$mode" == join ]]; then
  run_gate join Girth.CheckTrack2JoinLift Girth/CheckTrack2JoinLift.lean
fi
if [[ "$mode" == all || "$mode" == physical ]]; then
  run_gate physical Girth.CheckTrack2PhysicalAttachment Girth/CheckTrack2PhysicalAttachment.lean
fi

# Retain the integrated check for the active-girth, join, and increment gates.
if [[ "$mode" == all && "$failures" -eq 0 ]]; then
  run_gate integrated Girth.CheckTrack2Trace Girth/CheckTrack2Trace.lean
fi

echo "Track 2: $passes focused/full gate(s) passed, $failures failed."
if [[ "$failures" -ne 0 ]]; then
  exit 1
fi
echo "Kernel/axiom checks passed for checkout $(git rev-parse HEAD)."
