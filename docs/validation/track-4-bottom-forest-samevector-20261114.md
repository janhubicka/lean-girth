# Numbered Track 4 — actual bottom forest and same-vector conversion (2026-11-14)

**Status:** Source-only, **UNCOMPILED** Lean proof candidates. No exact-head Lean kernel or `#print axioms` execution. Do **not** promote validation marks or merge as a verified proof. GitHub workflow budget not used.

## Pinned references

- Lean base: `janhubicka/lean-girth/main@98e40142f95cf818f498ed21faf9302a50fe7832`. Current main `b0b3c49a7d2b47150f146df588b5868be9d6cce3` has disjoint later commits.
- Circulation manuscript snapshot: `janhubicka/girth/main@8c9cfa6eb6d817a08f3009fe048fc0be07426ece`, reachable-source SHA-256 `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
- Lean draft PR [#1064](https://github.com/janhubicka/lean-girth/pull/1064); TeX draft PR [#448](https://github.com/janhubicka/girth/pull/448); [Track issue #1055](https://github.com/janhubicka/lean-girth/issues/1055).

## Bottom proof, original B-label throughout

- **Real original length two:** `TrainBottomTwoLabelCoreIntersection`, `TrainActualBottomOwnerCoreSeparation`, `TrainActualBottomOriginalTwoCycleCore/All`. A zero-cut source uses the old one-picture theorem. Otherwise two original label carriers meet only in the attached core; strong original B-core boundary and A-strong core edge boundary plus A-linearity force an allowed intersection. The existing bottom two-member lemma produces a global supreme **original** designated copy. The distinct-double-wagon case is then impossible. No lower witness full girth is used.
- **Original length >=3:** `TrainFillingMixedNormalization` (existing) preserves connectors/order and supreme-label pullback. True geometric minimum owners plus exact attached bottom boundary and cut-connector geometry rule out mixed singleton occurrences. **Direct pointwise cut charging** uses `c_i+c_(i+1) <= w_i`, obtaining `2*#cuts <= twiceOrder`; avoids explicit segment-block counting. The actual reduced witness has at most q labels, and its local mixed forest gives genuine global supremacy even without pre-supposed A1 for a two-label reduct. Bottom plans are automatically short-only. Existing zero-, two-, and three-plus-cut source-transfer proofs then produce an original B-labelled supreme plan.
- **Full bottom one-step endpoint:** `attachedSelectedPicture_bottom_fullSystemGirth_of_localForest` (`TrainActualBottomFullSystemForestPreservation`). The actual local forest and physical gluing geometry are explicit; no local `FullSystemGirthGT` oracle.

## Honest F_t adapters

- **Selected non-one-edge local target:** `TrainActualWitnessBottomMixedForestBridge` converts genuine finite **sets of support pieces** through q into indexed `LocalForestThrough`, provided the local source has two distinct A-support edges and one representative is chosen per distinct **vertex image**. `activeGluingWitness_supportPiece_injective_of_distinct_images` proves support-piece injectivity follows from image-injectivity (a support piece stores the entire vertex carrier). `TrainActualBottomForestFromFiniteMixed` derives local A-linearity and strong images from the same q-level finite mixed forest and concludes output bottom full system girth.
- **One-edge local target:** `ForestConstantOneEdgeLocal` proves that arbitrarily repeated labels of the *same one-edge piece* form a forest via a star join tree. `activeGluingWitness_bottom_localForest_of_singleEdge` instantiates this in the literal local witness; `TrainActualBottomSingleEdgeLocalPreservation` supplies output bottom full system girth without a two-source-edge or image-injectivity premise. The finite conversion still needs to select this elementary witness for the one-edge active target; the manuscript cites Observation `obs:oneedgetrain`.
- **Why distinct supports matter otherwise:** if two different owners label the same multi-edge support, their intersection can be the entire multi-edge carrier, not a singleton or common single support edge. A finite **set** forest promise cannot be applied to this duplicated labelled pair. See issue comment [#6879461404](https://github.com/janhubicka/lean-girth/issues/1055#issuecomment-6879461404).

## Same-vector coordinate and parameter pass

- `attachedSelectedPicture_bottom_and_interior_of_sameVector`: bottom `q` from finite mixed forests, positive proper cuts at each exact `h_i` from the existing full-system variant.
- `attachedSelectedPicture_sameVector_bounds_and_parameters`: also derives actual adjacent part-intersection parameters from old/core adjacent parameters and positive-cut order-one bridges. Equality bottom and universal top are already handled by the intrinsic parameter theorem. No extra top system-girth coordinate is introduced.
- `ForestTailStage.withBottomSystemGirth`: a finite ForestTailStage already retains all positive bounds, selected labels, train restrictions, parameters, forests and partite structure. Adding bottom full system girth at `q` turns it into an OrderStage without changing those fields.
- `ForestTailStage.ramseyOrderPass_of_ready_bottom`: combines the existing finite selected Ramsey-arrow pass with an **explicit** terminal readiness-to-bottom criterion. This criterion is NOT proven merely by having a forest stage; it must follow from the actual finite sequence of one-step bottom preservations. This isolates the final nontrivial readiness invariant.

## Remaining independent tasks

1. **Exact-head local Lean compile**: `lake env lean CheckTrack4MinimumOwnerSwap.lean`, inspect every `#print axioms`; repair unknown identifiers and tactics (static checks are insufficient). No local Lean/lake/elan or usable network in the present runtime.
2. Adversarially check the full `F_t` witness selection: complete support-image distinctness, two distinct source A-edges in the nontrivial branch, one-edge active-target branch, strong partite embeddings, bottom and positive exact cutoffs, and all same-edge reflections.
3. Prove the actual **finite-pass Ready invariant** is preserved under each attachment and implies final bottom `FullSystemGirthGT q`. The preparatory one-step theorem is available as a draft; the final finite Ramsey arrow is already an established conditional pass.
4. Review the one-edge initial picture, top endpoint parameter conditions, final ordering/fine-part coarsening, and extraction of the selected **strong train** arrow.
5. Independent adverse audit and main integration only after kernel checks. Keep manuscript `thm:preservation`, `cor:coordinate`, and `prop:globalize` unpromoted.

## Reuse and size discipline

Existing checked modules reused rather than duplicated include `TrainFillingMixedNormalization`, `TrainCyclicOwnerIsolatedNonincrease`, `TrainActualCutIndexedBigCycle`, `ForestToSupremeBottom/Cycle`, `TrainActualZeroCutGlobalSupreme`, `TrainActualThreeCutOnePassSupreme`, `TrainActualTwoCutSymmetricShortSupreme`, `TrainActualTwoCutSingletonShortStandardTransfer`, `TrainActualIntrinsicParameters`, and `TrainRecursiveWitnessPass`. New source files are intended as small compositional interfaces, not replacements for the checked old proof.
