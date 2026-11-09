# Compact diagram validation, 9 November 2026

This branch starts validation of the compact manuscript after an independent
second audit. It is based on `2f900df5b3ee3c32e6471f143dd720bfea27781a`;
the manuscript baseline is girth commit
`fb53f5ae80dcac7f6c8c088decca85b5e6edd5be`.
Neither repository's main branch nor the ongoing validation branch is changed.

## Four checked components

| Module | New result | Boundary |
| --- | --- | --- |
| `CompactDiagramForest` | Allowed full overlaps on join-tree links imply the old all-pairs forest condition; physical-edge occurrences are connected. | Uses ambient linearity and running intersection; does not construct the free quotient. |
| `CompactForestGluing` | Joins two genuine forests by a link over their assembled singleton/empty overlap or retained whole-edge anchors. | No new singleton member nodes and no assumed all-pairs cross-intersection condition; full outer-tree induction remains separate. |
| `CompactInitialPicture` | Combines every proper-cut system bound, including the physical bottom cut, with the complete bottom mixed-forest assertion. | Derived from target girth and labelled target cuts; no universal-top bound is asserted. |
| `CompactPrivateExtension` | Restricts a strong copy of the disjoint wagon sum to each original wagon and constructs the direct private extensions. | No equal-size/equivalence hypothesis; relational wrapper explicitly retains the disjoint-support identity. |

All four modules compiled locally with Lean 4.35.0-rc3. Four focused check
files passed the strict axiom checker: **29 declarations in total**, including
regressions and reused interfaces. Their transitive axiom dependencies are
contained in `propext`, `Classical.choice`, and `Quot.sound`.
There are no admitted proofs or new axiom declarations in the new sources.

The finite regressions show that ambient linearity is essential and that
point-link gluing retains exactly the two existing chart labels. Detailed
scope and commands are recorded in [forest.md](forest.md),
[forest-gluing.md](forest-gluing.md), [initial-picture.md](initial-picture.md),
and [private-extension.md](private-extension.md).

## Reproduction

With the repository's pinned toolchain and dependencies installed, build the
four named `Girth.Compact...` modules and run the corresponding
`CheckCompact....lean` files. For each captured output, run
`python3 scripts/check_axioms.py OUTPUT CHECK_FILE`.

This session used the local official Linux toolchain and existing pinned
dependency cache. Only missing project imports were compiled; Mathlib was
not rebuilt. Lean calls used an explicit dependency search path and at most
two concurrent workers. The executable-location compatibility wrapper
described in [local-runtime.json](local-runtime.json) does not change Lean's
kernel or proof objects. The runtime and Lake version checks passed.

Final source hashes and each strict-check result are in
[validation-results.json](validation-results.json). The four axiom logs are
retained beside this report. A full-repository build was not run.

## What remains open

These are substantive bridges, not a complete formal proof of the draft.
The free-realization equivalence, complete finite leaf assembly and request
bookkeeping, prescribed-first-parameter Ramsey input, actual selected
contracted-copy realization in the global filling, and final recursive
witness assembly retain their separate obligations. Existing conditional
cycle-transfer results are not upgraded by these checks.

The direct-extension module repairs an actual marker mismatch found by the
second audit: the old uniform constructors required each original first
wagon to be equivalent to their whole disjoint sum. Their markers must be
replaced at the direct construction, while the remaining Ramsey and global
transport obligations remain visible.
