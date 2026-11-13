# Numbered validation tracks 1–8 — girth circulation revision (13 November 2026)

This is a **new** validation plan, not a renaming of legacy tracks A–G. Existing Lean proofs, historical checker files, and the old PR branches are retained until their replacements pass exact-head checks.

## Exact manuscript and kernel baselines

- Audited proposed manuscript: 41 pages, 69 numbered mathematical statements, 23 reachable TeX inputs.
- Canonical reachable-source SHA-256: `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
- Manuscript **frozen baseline**: [`8c9cfa6eb6d817a08f3009fe048fc0be07426ece`](https://github.com/janhubicka/girth/commit/8c9cfa6eb6d817a08f3009fe048fc0be07426ece) from merged PR #445, with exact source hash above. **Current editorially clarified `main`** is [`6e2048b7cbc6d16c27dfcdaf8e67924f5906f846`](https://github.com/janhubicka/girth/commit/6e2048b7cbc6d16c27dfcdaf8e67924f5906f846), after merged PRs #446 (Track 7), #449 (Track 8) and #447 (Track 3). These changes preserve labels and the validation markers, but the baseline SHA-256 is **not** the digest of the current edited source. Pre-tag `main` was `c195cdba`.
- `lean-girth` baseline: `e57c954c6417604d35332adfdf3304a225281eca`, pinned to `leanprover/lean4:v4.35.0-rc3`.
- The 23 reachable TeX inputs in merged PR #445 have byte-identical Git blobs to the audited archive. **Pin completed historical baseline certificates to `8c9cfa6e` and its digest.** For any claim about the now-current editorially clarified manuscript, separately pin `6e2048b7` and regenerate the current-source digest; no old source digest is reused for changed TeX.
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

## Branch policy for spawned tracks

Do **not** pre-create eight empty remote branches: `.github/workflows/lean.yml` runs a full Lean job on every branch push. Start from the current `lean-girth/main` after the documentation-only preparation commits, and publish a numbered branch only with its first useful change. Suggested names:

- `validation/1-closures-cutoff-three` (#1052)
- `validation/2-join-trees-forests` (#1053)
- `validation/3-wagons-linearity` (#1054)
- `validation/4-system-girth-conversion` (#1055)
- `validation/5-filling-cutoff-two` (#1056)
- `validation/6-refinements` (#1057)
- `validation/7-recursive-witness` (#1058)
- `validation/8-small-traces-theorem` (#1059)

Prior lettered branches remain as historical sources. **Do not cherry-pick a historical PR wholesale** before comparing exact shared files and hypotheses. Begin each numbered branch with a source-to-Lean statement mapping, record its base SHA, then import/reuse the necessary established declarations.

## Evening merge queue checkpoint (13 November)

- GitHub `lean-girth/main` advanced to `76bf2ac4648d4218e9a73823a16224a066a2b259` by fully green historical CI workflow-retry PR #1035. No proof source, Lean dependencies or strict axiom checker were changed by this PR.
- Obsolete #1030/#1033 retry PRs and #1022/#1031/#1037 proof stacks were closed. For the latter three, **every added Lean source/checker Git blob already matches current main**, and all their focused checker registrations exist on main. The closure is deduplication, not deletion or new validation.
- Numbered new Track 4/5/7/3 Lean PRs #1064/#1063/#1066/#1067 remain draft and **uncompiled** at exact head. Historical CI successes for the same component theorem do not certify these new wrappers.
- Manuscript editorial PRs #446/#449/#447 were merged after a static source/statement/marker check; **no fresh full TeX rebuild or Lean kernel verification** was executed for their combined current-main version in this checkpoint.
- Reuse-adjusted validation estimate stays approximately 56%; all eight numbered tracks remain open, and none is signed off by the new version's full Lean kernel.
