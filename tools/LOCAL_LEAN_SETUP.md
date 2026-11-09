# Reusable offline Lean setup for `lean-girth` (2026-11-09)

This is a **temporary, non-merge setup branch**. It uses the repository's exact
`lean-toolchain` and resolved `lake-manifest.json`, including the pinned
`partite-construction` and `successor-tree-lean` projects; no dependency is upgraded.
It packages a trusted **Linux x86-64** Lean compiler and actual compiled mathlib
and project dependencies on a GitHub-hosted Ubuntu runner. The artifacts are
split into at most 300-MB files because larger individual downloads can fail
through the connector. All chunks and full streams have SHA-256 checksums.

After a successful `Temporary lean-girth offline Linux workspace` Actions run:

```bash
gh run download RUN_ID --repo janhubicka/lean-girth --dir ./girth-artifacts
bash tools/restore_local_lean_girth.sh --verify-only ./girth-artifacts ./unused
bash tools/restore_local_lean_girth.sh ./girth-artifacts ./lean-girth-local
source ./lean-girth-local/env.sh
cd ./lean-girth-local/project
LEAN_NUM_THREADS=1 lake build Girth.TrainActualOneLevelGirthIntrinsic
lake env lean CheckActualOneLevelGirthIntrinsic.lean | tee CheckActualOneLevelGirthIntrinsic.log
python3 scripts/check_axioms.py CheckActualOneLevelGirthIntrinsic.log CheckActualOneLevelGirthIntrinsic.lean
```

The restore script refuses overwriting an existing destination, validates
checksums **before** extraction, verifies the pinned toolchain, and compiles a
real mathlib smoke test. A successful byte transfer or archive verification is
**not** itself a successful project build. For full validation use the repository's
`scripts/check_track_d.sh` and CI full `Girth` build. The project snapshot
records `SOURCE_SHA`; do not mistake it for another branch revision.

If container shell execution itself fails (even `/bin/echo`), this cannot
be repaired inside Lean. The matching GitHub Actions build remains a genuine,
separately verifiable compilation until local execution is operational.

Do not merge the temporary bundle workflow into the circulation branch.
