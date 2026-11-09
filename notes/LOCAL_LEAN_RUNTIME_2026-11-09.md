# Local Lean runtime for the simultaneous-transfer audit

9 November 2026. This records runtime installation and smoke checks, not
validation of the circulation theorem. The focused proof gate is
`scripts/validate_simultaneous_transfer.sh`; its own exit status and logs
determine which project checks passed.

## Exact runtime and dependencies

- Repository pin: `leanprover/lean4:v4.35.0-rc3`.
- Executed Lean: `4.35.0-rc3`, Linux x86-64, commit
  `470d5ce1400764999581fd26d5d72b00d990b0f4`.
- Executed Lake: `5.0.0-src+470d5ce`.
- Official Linux compiler archive SHA256:
  `1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997`.
- Compiler transport: `janhubicka/lean-gluing-eppa`, successful Ubuntu
  workflow run `42512209025`, artifacts `13629344423` and `13630395948`.
  Both ZIPs passed CRC checks; the concatenated archive matched the hash
  above before extraction. The official compiler and library bytes were
  not modified.
- Matching private dependency cache: mathlib
  `5bd58ac291422a21f412ae354c91e7d172255a2c`, partite-construction
  `d2394f65861528f27d68c4a42042285dafef301d`, and successor-tree-lean
  `f9513be1d92782e7a8c45916d32e6e11dc0e0dcf`, with the remaining packages
  recorded by the local `lake-manifest.json`.

The cache was copied into this task's checkout. Other tasks' dependency
trees were left untouched. Its inherited Batteries warning concerns only
missing `docs/README.md`; inspection found no Batteries proof-source diff.
Cache presence is not a claim that every project module has been checked.

## Real smoke checks

Both direct Lean execution and `lake env lean` succeeded with a file
importing `Mathlib.Data.Finset.Basic`, proving `(2 : Nat) + 2 = 4` by
`decide`, and printing the axioms of `Nat.add_comm` (none). A second file
importing `Mathlib.Tactic` proved `a < b` from `a + 1 ≤ b` using `omega`.
These were real kernel runs, not mock executables or source-only checks.

## Portable use

Install the exact repository toolchain and restore the pinned Lake
dependencies and compiled mathlib cache. Do not run `lake update` merely
to start validation, and do not replace the repository pins by newer
versions. With `lean` and `lake` on `PATH`, run from the repository:

```bash
LEAN_NUM_THREADS=1 bash scripts/validate_simultaneous_transfer.sh
# Optional log destination:
LEAN_NUM_THREADS=1 bash scripts/validate_simultaneous_transfer.sh /tmp/girth-audit-logs
# Append additional branch targets or root checks:
LEAN_NUM_THREADS=1 bash scripts/validate_simultaneous_transfer.sh \
  --target Girth.AdditionalModule --check CheckAdditional.lean
```

The script checks `lake env lean --version` against `lean-toolchain`,
builds the three relevant Lean targets with `lake build +Module`, and
runs the seven new root check files through the strict axiom checker.
`set -euo pipefail` preserves build/check failures across `tee` pipelines.
The checker permits only `propext`, `Classical.choice`, and `Quot.sound`,
and rejects missing requested declarations. Logs default to
`local-validation/simultaneous`. This is a focused gate, not a substitute
for a subsequent full-library build and wider regression suite.

Only a fully successful run writes `result.json`, containing the toolchain
output, target list, audited filenames and declaration counts, and SHA256
hashes for checked roots and their transitive local Girth imports. Hashes
are captured before compilation and verified unchanged afterwards; a
failed rerun removes any prior success result. The full axiom output and
exact per-check counts remain in the individual logs.

## This workspace

The installed runtime is outside the Git repository, at
`/workspace/scratch/095f642caf71/runtime`. The local setup command is:

```bash
source /workspace/scratch/095f642caf71/runtime/env.sh
cd /workspace/scratch/095f642caf71/lean-girth
bash scripts/validate_simultaneous_transfer.sh
```

The environment sets `LEAN_SYSROOT`, prepends the official toolchain's
`bin` directory to `PATH`, and sets `LEAN_NUM_THREADS=1`. The observed
memory cgroup limit is 8 GiB; at most two Lean proof workers should run
concurrently initially. Lake 5 has no `-j` flag. Avoid rebuilding mathlib
when matching cached objects already exist.

### Narrow process-path compatibility workaround

This container's `getpid()` reports its namespace-local PID, whereas the
exposed numeric `/proc` directories use a different PID namespace.
Consequently `/proc/<getpid()>/exe` returns `ENOENT`, while
`/proc/self/exe` resolves correctly. Lean 4.35's Linux executable-location
code uses the former, causing `failed to locate application` before even
`lean --version` runs.

The workspace environment loads `runtime/self_exe_compat.so` through
`LD_PRELOAD`. Its complete relevant operation is:

```c
ssize_t readlink(const char *path, char *buffer, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t) = NULL;
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char self_path[64];
    snprintf(self_path, sizeof(self_path), "/proc/%ld/exe", (long)getpid());
    return real_readlink(strcmp(path, self_path) == 0 ? "/proc/self/exe" : path,
                         buffer, size);
}
```

The source defines `_GNU_SOURCE` and includes `dlfcn.h`, `stdio.h`,
`string.h`, and `unistd.h`. It is compiled with
`cc -shared -fPIC -O2 -Wall -Wextra self_exe_compat.c -o self_exe_compat.so -ldl`.
Only the exact own-process executable lookup is redirected; every other
`readlink` call is forwarded unchanged. No Lean code, proof object,
kernel rule, or axiom is patched. Ordinary hosts with a coherent `/proc`
namespace need no shim and should not set this `LD_PRELOAD` value.
