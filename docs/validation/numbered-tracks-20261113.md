# Numbered validation tracks 1–8 — girth circulation revision (13 November 2026)

This is a **new** validation plan, not a renaming of legacy tracks A–G. Existing Lean proofs, historical checker files, and the old PR branches are retained until their replacements pass exact-head checks.

## Exact manuscript and kernel baselines

- Audited proposed manuscript: 41 pages, 69 numbered mathematical statements, 23 reachable TeX inputs.
- Canonical reachable-source SHA-256: `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
- Manuscript **current `main`** after audited tag-first merge: [`8c9cfa6eb6d817a08f3009fe048fc0be07426ece`](https://github.com/janhubicka/girth/commit/8c9cfa6eb6d817a08f3009fe048fc0be07426ece), from merged [PR #445](https://github.com/janhubicka/girth/pull/445). Pre-merge `main` was `c195cdbaaabbafe53ac313fd283ffcaa0a159494`.
- `lean-girth` baseline: `e57c954c6417604d35332adfdf3304a225281eca`, pinned to `leanprover/lean4:v4.35.0-rc3`.
- The 23 reachable TeX inputs in merged PR #445 have byte-identical Git blobs to the audited archive. **Pin all new validation to the merged commit** `8c9cfa6eb6d817a08f3009fe048fc0be07426ece` and the manifest digest above, rather than the old PR head.
- The annotated tag [`girth-main-before-eppa-preparation-20261113-c195cdba`](https://github.com/janhubicka/girth/tree/girth-main-before-eppa-preparation-20261113-c195cdba) was verified to dereference to the exact old `main` commit `c195cdbaaabbafe53ac313fd283ffcaa0a159494` **before** PR #445 was merged. The backup branch remains available. The required safeguard is satisfied.
- [Programme index issue #1060](https://github.com/janhubicka/lean-girth/issues/1060). The previous digest in that issue refers to an earlier, unexported candidate; use the exact digest above.

## Tracks to spawn

| New track | Issue | Scope | Earliest verified/reusable starting point | Primary new obligation |
|---|---|---|---|---|
| **1** | [#1052](https://github.com/janhubicka/lean-girth/issues/1052) | Canonical closure, Ramsey input, cutoff-three case without trains | `Girth/FunctionalEHNClass.lean`, `Girth/TargetClosure.lean`, `Girth/TrainRecursiveBaseRamsey.lean` | Canonical optional unary closure, triangle-free class, actual indexed witness and train-free q=3 construction |
| **2** | [#1053](https://github.com/janhubicka/lean-girth/issues/1053) | Join-tree lifting and direct forest increment | `Girth/ForestJoinLiftLinear.lean`, `Girth/ForestAuxiliaryDeletion.lean`, boundary/strong-attachment geometry | Post-completion one-helper-per-missing-vertex adapter; rigorous set-indexed output and active girth from forest extension |
| **3** | [#1054](https://github.com/janhubicka/lean-girth/issues/1054) | Generated wagons, parameters, output linearity | `Girth/TrainActualASupportTrainTransport.lean`, `Girth/TrainSelectedPictureLinearPretrain.lean` and all-level geometry | Exact full-hypergraph adapters; no circular use of output girth |
| **4** | [#1055](https://github.com/janhubicka/lean-girth/issues/1055) | Full-system and bottom-forest cycle preservation | `Girth/TrainArbitraryLegalReplacementComplete.lean` and candidate PRs #1022, #1031 | Reuse exact one-level theorem; independently discharge the weaker bottom-forest alternative and same-vector conversion |
| **5** | [#1056](https://github.com/janhubicka/lean-girth/issues/1056) | Filling and direct cutoff two | `Girth/TrainFillingSystemGirth.lean`, `Girth/TrainFillingParentwiseChoiceRealization.lean` | Construct the actual parent-indexed filled target, selected colour-word and embedding maps |
| **6** | [#1057](https://github.com/janhubicka/lean-girth/issues/1057) | Refinement and forgetting | `Girth/TrainRecursiveRefinementGirthGain.lean`, retained-cut modules | First certify old-strength g+1 adapter; then prove local 2g+1 and global cap min(2g+1,h1) |
| **7** | [#1058](https://github.com/janhubicka/lean-girth/issues/1058) | Full recursive witness construction | `Girth/TrainRecursiveFineWitnessStep.lean`, `Girth/TrainRecursiveCoarsenedSelectedFamilyArrow.lean` | Construct genuine indexed partite lower witness and output tail supremeness; remove all current-rank oracles |
| **8** | [#1059](https://github.com/janhubicka/lean-girth/issues/1059) | Small traces and final structural theorem | `Girth/SupportedTree.lean`, `Girth/ForestTreeRewire.lean`, existing decoration and partite fusion | Small-trace chordality/conformality, nonempty trace bound, induced relational extraction |

## Essential audit distinctions

**Track 2:** `forestOfCopies_lift_local_of_linear` assumes a connector at *every* singleton separator. The revised English leaf argument does not. Add one helper for each missing vertex **after** local completion, not one per separator link. Never infer arbitrary subfamily heredity of forests.

**Tracks 3–4:** full-system preservation in PR [#1022](https://github.com/janhubicka/lean-girth/pull/1022) is a candidate theorem with historical successful exact-head CI (Lean run 42572239970; focused run 42572239964); the PR remains unmerged and was not rebuilt against this documentation revision. The theorem assumes actual old and lower-witness bounds, output linearity, two-edge selected copies, full strongness and exact train restrictions. More intrinsic follow-ups [#1031](https://github.com/janhubicka/lean-girth/pull/1031) and [#1036](https://github.com/janhubicka/lean-girth/pull/1036) are stacked drafts, not newly certified on main. A local reduced gluing-copy label is **not** an original designated B-copy.

**Track 5:** `TrainFilling.filled_fullSystemGirthGT` is already usable under its printed record, old girth and new-edge linearity. `ParentwiseRealization` is a *hypothesis record*; its concrete vertex/edge/wagon maps still need construction. Do not delete ambient edges.

**Track 6:** the checked old module gives g+1 inside first wagons and globally only under universal first relation. The stronger 2g+1 estimate is unverified; for nonempty tail the global threshold is limited by the retained first cutoff. This strengthening should not block the original recursion.

**Track 7:** `ForestTailStage.refiningPictureStep_of_fineWitness` is conditional on a true indexed fine witness, arrow and output-tail SupremeCycleBound. `selectedCopy_notPartiteGluing_of_nontrivialActive` rules out the naive small-base reindexing, not the established **larger-base part-coarsening** approach.

**Track 8:** the exact `|Z|` bound is for distinct maximal **nonempty** traces. The case `Z=∅` uses no selected members. The conclusion uses the stronger internal forest-extension invariant, not only an embedding into a supported tree.

## Completion policy and cleanup

1. Keep existing `Girth/*.lean` proofs and the old `Check*.lean` gates. They are the reusable proof library; no mass deletion or renaming before a replacement has a complete exact-interface certificate.
2. A per-track validation mark must name the manuscript label, source digest, Lean module and declaration, **commit**, fully elaborated hypotheses, exact adapter, local build, and `#print axioms`. Distinguish conditional verified lemmas from closed theorems.
3. No `sorryAx`, unsupported axiom, artificial extra output bound or unconstructed witness may close a track. The external Evans–Hubička–Nešetřil input remains explicit.
4. Prefer local Lean; do not trigger paid GitHub Actions solely for this plan. Existing CI successes are historical, not a new build.
5. Legacy lettered tracks remain historical. New work is labelled **Track 1** to **Track 8** only.

**Status:** Manuscript PR #445 is merged and pinned. Repository preparation and historic PR cleanup are complete; **no new Lean kernel verification of the 41-page revision** is asserted here.
