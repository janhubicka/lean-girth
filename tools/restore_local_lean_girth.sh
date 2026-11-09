#!/usr/bin/env bash
# Offline restore for the EXACT Lean + Lake bundle prepared by the temporary girth workflow.
# Inputs: gh run download RUN_ID -R janhubicka/lean-girth -D ARTIFACTS
#         bash tools/restore_local_lean_girth.sh ARTIFACTS FRESH-ROOT
set -euo pipefail
VERIFY=0
if [[ ${1:-} == --verify-only ]]; then VERIFY=1; shift; fi
if [[ $# != 2 ]]; then
  echo "Usage: $0 [--verify-only] DOWNLOADED-ARTIFACTS-DIR FRESH-ROOT" >&2
  exit 2
fi
INPUT=$1
ROOT=$2
test -d "$INPUT"
for tool in python3 sha256sum find sort tar zstd; do command -v "$tool" >/dev/null; done
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT
# Unpack files as produced by 'gh run download': one folder per named artifact.
# Reject duplicate names so artifacts from multiple runs cannot silently mix.
python3 - "$INPUT" "$STAGE" <<'PY'
from pathlib import Path
import os, sys
root, dest = (Path(x).resolve() for x in sys.argv[1:])
required = {
  'SOURCE_SHA', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
  'source.tar.zst', 'SOURCE_SHA256SUMS', 'LEAN_SHA256SUMS',
  'LEAN_PART_SHA256SUMS', 'LAKE_SHA256SUMS', 'LAKE_PART_SHA256SUMS'
}
seen = set()
for p in root.rglob('*'):
    if not p.is_file():
        continue
    name = p.name
    if name not in required and not (name.startswith('lean.tar.zst.part-') or name.startswith('lake.tar.zst.part-')):
        continue
    if name in seen:
        raise SystemExit('Ambiguous duplicated input: '+name)
    seen.add(name)
    os.symlink(p, dest / name)
if not required.issubset(seen):
    raise SystemExit('Missing transport metadata: '+str(sorted(required-seen)))
for prefix in ('lean','lake'):
    parts = sorted(x for x in seen if x.startswith(prefix+'.tar.zst.part-'))
    if not parts or parts != [f'{prefix}.tar.zst.part-{i:02d}' for i in range(len(parts))]:
        raise SystemExit('Nonconsecutive '+prefix+' chunks')
print('Located', len(seen), 'verified-bundle inputs')
PY
cd "$STAGE"
test "$(cat lean-toolchain)" = 'leanprover/lean4:v4.35.0-rc3'
sha256sum -c SOURCE_SHA256SUMS
sha256sum -c LEAN_PART_SHA256SUMS
sha256sum -c LAKE_PART_SHA256SUMS
# Verify hashes of each reconstructed compressed stream before any extraction.
EXPECTED_LEAN=$(awk '$2=="lean-4.35.0-rc3-linux.tar.zst" {print $1}' LEAN_SHA256SUMS)
EXPECTED_LAKE=$(awk '$2=="lake.tar.zst" {print $1}' LAKE_SHA256SUMS)
test "$EXPECTED_LEAN" = 1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997
test "$(cat lean.tar.zst.part-* | sha256sum | awk '{print $1}')" = "$EXPECTED_LEAN"
test "$(cat lake.tar.zst.part-* | sha256sum | awk '{print $1}')" = "$EXPECTED_LAKE"
if [[ $VERIFY == 1 ]]; then
  echo "All source, Linux compiler, workspace, and chunk SHA-256 checks passed."
  exit 0
fi
if [[ -e "$ROOT" ]]; then
  echo "Refusing to overwrite existing target $ROOT" >&2
  exit 3
fi
mkdir -p "$ROOT/project" "$ROOT/toolchain"
ROOT=$(cd "$ROOT" && pwd -P)
# Only archives created by our trusted workflow and hash checked above are unpacked.
zstd -dc source.tar.zst | tar --no-same-owner -xf - -C "$ROOT/project"
cat lean.tar.zst.part-* | zstd -dc | tar --no-same-owner -xf - -C "$ROOT/toolchain"
cat lake.tar.zst.part-* | zstd -dc | tar --no-same-owner -xf - -C "$ROOT/project"
cmp "$ROOT/project/lean-toolchain" "$STAGE/lean-toolchain"
cmp "$ROOT/project/lakefile.toml" "$STAGE/lakefile.toml"
cmp "$ROOT/project/lake-manifest.json" "$STAGE/lake-manifest.json"
cp "$STAGE/SOURCE_SHA" "$ROOT/SOURCE_SHA"
T="$ROOT/toolchain/lean-4.35.0-rc3-linux"
test -x "$T/bin/lean"
test -x "$T/bin/lake"
cat > "$ROOT/env.sh" <<EOF
export LEAN_SYSROOT='$T'
export PATH="\$LEAN_SYSROOT/bin:\$PATH"
export LEAN_NUM_THREADS=1
EOF
source "$ROOT/env.sh"
cd "$ROOT/project"
lean --version
lake --version
printf '%s\n' 'import Mathlib.Data.Finset.Basic' '#check Nat.add_comm' 'example : (2 : Nat) + 2 = 4 := by decide' > OfflineMathlibSmoke.lean
lake env lean OfflineMathlibSmoke.lean
rm OfflineMathlibSmoke.lean
echo "Real local Lean/mathlib smoke test passed; project source SHA: $(cat "$ROOT/SOURCE_SHA")"
echo "Run: source $ROOT/env.sh"
echo "Then: cd $ROOT/project && LEAN_NUM_THREADS=1 lake build Girth.TrainActualOneLevelGirthIntrinsic"
