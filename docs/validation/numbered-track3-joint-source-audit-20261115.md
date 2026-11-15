# Numbered Track 3 — exact source-only joint geometry and parameter audit

**Date:** 15 November 2026. **Status:** source audit only, NOT new Lean compilation.

**Repository baselines inspected:** `janhubicka/lean-girth/main@8607a3cb826d9b631aba8dfe863de45c871942f6`; manuscript `janhubicka/girth/main@365376622359a809b59cae5058fbb7628da23c8e`. The manuscript's Track 3 changes in PRs #447, #451, #459, #462, #466 are merged. The live Lean Track 3 joint wrapper is a draft PR #1067.

## Historical certified dependencies

The following source blobs on current Lean main were **independently compared byte-for-byte** with commits that had successful Lean runs. This historical evidence applies to the imported components, not to the newly authored composition.

| Source module | Git blob SHA | Historical checked commit |
| --- | --- | --- |
| `Girth/TrainSelectedPictureIntrinsicGeometry.lean` | `365ffdfed879b2e86691a49ff020d74b8b938e78` | merged PR #694, `e1719e1a42748908729b760cc6549d99125f9ee0` |
| `Girth/TrainSelectedPictureStageGeometry.lean` | `310bf6dfad6fad28b7a476fdf4e12d37d329b8f3` | merged PR #694, same exact head |
| `Girth/TrainActiveGluingWitness.lean` | `b23a6c70538c932faad5a1c308928e2823a9ae20` | merged PR #694, same exact head |
| `Girth/TrainSharedSupportInteriorCompatibility.lean` | `ac7b8c3751c894e4aeaf1a1060a81c8c229b4501` | merged PR #694, same exact head |
| `Girth/TrainActualIntrinsicParameters.lean` | `50157b3fd7019e7cec53141cc461a1fb6014bc63` | merged PR #670, `e2d43f823f5164213ce780d19879555b5c1b7787` |

Exact-head historical successful workflow runs: `40983362500`, `40983360921` (PR #694), and `40831595601` (PR #670). They prove kernel elaboration of their historical targets, **not** of this PR. The direct `#print axioms` gate for generated actual support and core/standard restrictions was merged as PR #1065; its on-main source is `CheckTrack3ActualSupportAndRestrictions.lean` blob `9d63875834dd55ba46cb79dce7661a0f1105ebbd`.

## Audited proof dependency diagram

```
Real partite active attachment with shared physical A-support
        |
        +-- exact interior shared-wagon reflection + preservation
        |     (automatic bottom equality and universal top)
        |
        +-- old A-support LinearPretrain at interior cuts
        |     from stage.tailGirth, via j.castSucc = mu
        |
        +-- old actual A-support AdjacentParameters
        |     from stage.parameters
        |
        +-- actual local lower witness U, partite R, selected index family f
              +-- original core AdjacentParameters
              +-- local FullSystemGirthGT (g mu), g mu >= 2
                    |-- core physical linearity and whole image A-strongness
                    |-- local order-two pieces -> all cut wagon linearity
                    |-- order-one pairwise bridges -> adjacent parameters
        |
        v
Actual attached A-support output:
    ALinear; LinearPretrain at every cut;
    every complete wagon A-strong; all AdjacentParameters
```

No output system-girth, no asserted existence of the lower witness, no pruning of ambient A-copies, and no substitution of equal vertex carriers for wagon-class equality. Source labels are kept separate from designated-copy indices. The precise `OrderOneData.bound_of_fullSystemGirth_ge_one` reduction is in `Girth/TrainFullSystemGirthParameter.lean` (current blob `a612480ac61fac7091b7839ad7dfeab690955df0`). Its output is a **pairwise** bridge for distinct competing labels, not an invalid isolated-label bridge.

## New declarations in draft PR #1067 (all uncompiled)

1. `track3_partiteInduce_toRelStructure_eq`: `rfl` adapter for partite induced relation.
2. `track3_partiteAttachment_toRelStructure_eq`: `rfl` adapter for the complete free attachment on the same vertices.
3. `track3_joint_geometry_and_parameters`: height at least two, complete actual output geometry and all parameters from one source witness.
4. `track3_height_one_geometry_and_parameters`: height one, explicit old/core A-linearity and strong gluing images, no interior girth coordinate.
5. `TrainRecursiveWitness.ForestTailStage.activeAttachment_joint_geometry_and_parameters_of_two_le_height`: takes the old geometry and parameters from a *real* `ForestTailStage`, retaining all witness hypotheses.
6. `TrainRecursiveWitness.ForestTailStage.activeAttachment_joint_geometry_and_parameters_of_height_one`: on a real length-one stage, obtains old A-linearity and old adjacent parameters from `stage.aLinear` and `stage.parameters`; the core's A-linearity, full gluing-image strongness and core parameters remain explicit because no interior source girth coordinate exists.

The exact underlying `Partite.System.induce`, `Partite.Attachment.Vertex`, and `Partite.Attachment.attach.toRelStructure` definitions were inspected at the **pinned** dependency `partite-construction@d2394f65861528f27d68c4a42042285dafef301d`. The two `rfl` adapters are justified at the source level, but must still be elaborated.

## Validation gates (do not bypass)

- [ ] **Lean elaboration:** `lake build Girth.TrainTrack3JointGeometryParameters Girth.TrainTrack3StageJointGeometryParameters`.
- [ ] **Strict axiom check:** `lake env lean CheckTrack3JointGeometryParameters.lean`, then `python3 scripts/check_axioms.py <log> CheckTrack3JointGeometryParameters.lean`; alternatively `bash scripts/check_track3_joint.sh`, which performs both.
- [ ] **Source theorem comparison:** inspect Lean-printed hypothesis types and conclusion, especially shared relation reflection, genuine partite/relational attachment definitional equality, actual complete carrier, and `m=1` vs `m>=2`.
- [ ] **Independent prose audit:** ensure the compressed two-arc cycle argument under `lem:outlinear` is covered by the longer historical three-/four-label proof and neither silently assumes output girth.
- [ ] **Manuscript compile:** full TeX build of the merged main, not just source delimiter checks.

The runtime inspected for this audit has no `lean`, `lake`, `elan`, or restored matching Mathlib artifacts. No workflow was dispatched and no successful new exact-head run exists here. **All six new declarations remain candidate, not kernel-verified.**
