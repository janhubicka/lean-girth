#!/usr/bin/env bash
# Focused local gate for the branch-only simultaneous-transfer proposal.
# Requires the repository-pinned Lean and restored Lake dependencies.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd "$repo_root"
targets=(
  Girth.TrainActualCirculationCycleTransfer
  Girth.TrainEndpointGeometry
  Girth.UntouchedGirthTransversalBridge
)
checks=(
  CheckSimultaneousSegmentClassification.lean
  CheckActualSimultaneousSegmentTransfer.lean
  CheckActualOriginalTwoCycleSupreme.lean
  CheckTwoCutGeometricSupreme.lean
  CheckActualBottomReducedTransfer.lean
  CheckActualCirculationCycleTransfer.lean
  CheckSimplifiedCirculationInterfaces.lean
)
log_dir=local-validation/simultaneous
if [[ $# -gt 0 && $1 != --* ]]; then log_dir=$1; shift; fi
while [[ $# -gt 0 ]]; do
  case "$1" in
    --target) targets+=("${2:?--target requires a module}"); shift 2 ;;
    --check) checks+=("${2:?--check requires a root Lean file}"); shift 2 ;;
    *) echo "Usage: $0 [LOG_DIR] [--target MODULE] [--check ROOT.lean]" >&2; exit 2 ;;
  esac
done
for source in "${checks[@]}"; do
  if [[ "$source" == */* || "$source" != *.lean || ! -f "$source" ]]; then
    echo "Expected an existing repository-root Lean check: $source" >&2
    exit 2
  fi
done
mkdir -p -- "$log_dir"
log_dir=$(cd -- "$log_dir" && pwd -P)
# A failed rerun must not leave a previous success manifest in place.
rm -f -- "$log_dir/result.json"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}

pin=$(tr -d '\r\n' < lean-toolchain)
case "$pin" in
  leanprover/lean4:v*) expected_version=${pin#leanprover/lean4:v} ;;
  *) echo "Unsupported non-version toolchain pin: $pin" >&2; exit 2 ;;
esac
version=$(lake env lean --version 2>&1 | tee "$log_dir/toolchain.log")
if [[ "$version" != *"Lean (version $expected_version,"* ]]; then
  echo "Lean version does not match repository pin $pin" >&2
  exit 2
fi
{
  git rev-parse HEAD
  git status --short
  printf 'Toolchain pin: %s\nLEAN_NUM_THREADS: %s\n' "$pin" "$LEAN_NUM_THREADS"
} > "$log_dir/source-state.log"

write_manifest() {
  python3 - "$1" "$log_dir" "${targets[@]}" -- "${checks[@]}" <<'PY'
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

mode, directory, *arguments = sys.argv[1:]
log_dir = pathlib.Path(directory)
separator = arguments.index("--")
targets, checks = arguments[:separator], arguments[separator + 1:]
pending = [pathlib.Path(name.replace(".", "/") + ".lean") for name in targets]
pending.extend(map(pathlib.Path, checks))
hashes = {}
while pending:
    path = pending.pop()
    key = path.as_posix()
    if key in hashes:
        continue
    data = path.read_bytes()
    hashes[key] = hashlib.sha256(data).hexdigest()
    # Local Girth imports are declared one per line in this repository.
    for module in re.findall(r"^\s*(?:public\s+)?import\s+(Girth\.[\w.]+)",
                             data.decode(), re.M):
        pending.append(pathlib.Path(module.replace(".", "/") + ".lean"))
hashes = dict(sorted(hashes.items()))
snapshot = log_dir / "source-sha256.json"
if mode == "snapshot":
    snapshot.write_text(json.dumps(hashes, indent=2) + "\n")
    raise SystemExit(0)
if hashes != json.loads(snapshot.read_text()):
    raise SystemExit("Local checked sources changed during validation; rerun the gate.")
audits = []
for source in checks:
    counts = re.findall(r"^Checked (\d+) declarations; only the standard logical axioms occur\.$",
                        (log_dir / (pathlib.Path(source).stem + ".axioms.log")).read_text(), re.M)
    if len(counts) != 1:
        raise SystemExit(f"Missing or ambiguous successful strict audit for {source}")
    audits.append({"source": source, "declaration_count": int(counts[0])})
result = {
    "status": "passed",
    "completed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "toolchain_pin": pathlib.Path("lean-toolchain").read_text().strip(),
    "toolchain_output": (log_dir / "toolchain.log").read_text().strip(),
    "built_targets": targets,
    "audits": audits,
    "check_count": len(audits),
    "declaration_count_sum": sum(audit["declaration_count"] for audit in audits),
    "source_sha256": hashes,
}
temporary = log_dir / "result.json.tmp"
temporary.write_text(json.dumps(result, indent=2) + "\n")
temporary.replace(log_dir / "result.json")
PY
}

write_manifest snapshot
for target in "${targets[@]}"; do
  lake build "+$target" 2>&1 | tee "$log_dir/build-$target.log"
done

for source in "${checks[@]}"; do
  log="$log_dir/${source%.lean}.log"
  lake env lean "$source" 2>&1 | tee "$log"
  # check_axioms.py rejects missing declarations and every nonstandard axiom,
  # including sorryAx. Keep Python assertions enabled even in a caller's env.
  PYTHONOPTIMIZE=0 python3 scripts/check_axioms.py "$log" "$source" \
    2>&1 | tee "$log_dir/${source%.lean}.axioms.log"
done

write_manifest success
printf 'Focused simultaneous-transfer build and %s strict axiom audits passed.\n' "${#checks[@]}"
printf 'Logs: %s\n' "$log_dir"
