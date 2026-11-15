# Track 4 — coverage-free standalone F_t => R_t (15 November 2026)

**Status: substantial SOURCE-LEVEL mathematical Lean candidates, NOT compiled.**
Draft PR [lean-girth #1064](https://github.com/janhubicka/lean-girth/pull/1064); manuscript wording in [girth #448](https://github.com/janhubicka/girth/pull/448); work queue [issue #1055](https://github.com/janhubicka/lean-girth/issues/1055). All commits are [skip ci]. Do not promote validation markers or merge as verified without the exact-head local Lean build and axiom audit.

## The essential invariant mismatch

The circulation definition of F_t promises a selected physical edge-colouring Ramsey family, complete mixed finite-SET support forests through q, A-strong order-/part-preserving selected train embeddings (one per image), original intersection parameters and exact positive proper-cut full system girth. It does NOT promise any form of mixed irreducible coverage of the local witness by A- or selected B-copies.

The existing checked recursive ForestTailStage additionally stores mixedCoverage. At q=2 this extra property cannot be inferred from F_2, and even total A-extension of core irreducibles can be impossible under A-strong selected embeddings. The finite K4 triple construction and general A-strong no-go lemma are detailed in [the q2 obstruction note](./track-4-q2-core-coverage-obstruction-20261115.md).

Therefore there are TWO mathematically different paths:

1. When the local object is a GENUINELY constructed selected lower ForestTailStage, its extra mixedCoverage field may legitimately be used. The nested selected-target-or-A core argument in TrainSelectedMixedCoreAttachment and the mixed bounds/stage constructor are valid conditional source candidates even at q=2.
2. For the STANDALONE implication F_t=>R_t from an ARBITRARY F_t witness, one must not assume mixedCoverage. The coverage-free stage below is designed precisely for this weaker and sufficient promise.

## Coverage-free stage and finite selected Ramsey pass

- TrainCoverageFreeForestStage.lean defines CoverageFree.ForestStage and CoverageFree.OrderStage, copying ALL checked recursive stage fields except mixedCoverage. It retains the complete physical edge train, selected B labels, A-strongness, finite mixed forests, actual support nonempty/vertex coverage, part parameters and positive system-girth bounds. ForestStage.ofStrong forgets only mixed coverage, ForestStage.withMixedCoverage requires an ACTUAL proof to recover it, and ForestStage.withBottom adds bottom full system girth without introducing coverage.
- TrainCoverageFreeFinitePass.lean ports the checked finitePass/allProjections/ramseyPass, selected TransitionEmbedding, PictureStep and DesignatedArrow arguments WITHOUT any change to the mathematical proofs except replacing ForestTailStage with ForestStage. A static comparison to the checked TrainRecursiveWitnessPass source confirms the entire copied finite-pass section is token-identical under this renaming.
- TrainCoverageFreeOrderPass.lean records the genuine readiness as bottom full system girth at q plus selected lifts of each prescribed B-base copy. Every selected transition preserves base coverage. The final selected Ramsey arrow gives an A-strong B-copy with all target train relations reflected, without mixed irreducible coverage.
- TrainCoverageFreeComparison.lean maps checked stronger stages and their transitions/PictureSteps/DesignatedArrows literally into the coverage-free ones. The new finite pass is therefore a conservative weakening of the checked combinatorial argument.

## The actual standalone one-step picture preservation

- TrainCoverageFreeBottomIncrement.lean ports the checked physical bottom forest increment theorem, which NEVER used mixedCoverage, to the weaker old stage. It produces full ambient A-support girth >q, mixed finite-SET forest of selected output B-pieces plus all ambient A-edges through SAME q, and A-strongness of every transported original selected B-label.
- TrainCoverageFreeAttachment.lean ports the genuine selected physical next-stage assembly, TransitionEmbedding and Ramsey PictureStep with NO coreMixedCoverage or IrreduciblesExtendTo A E field. Its new ActiveAttachmentBounds requires only nonempty physical local A-support and coverage of local core vertices by actual A-edges, alongside all the unchanged selected/partite/train/forest/girth/parameter/tail fields. These are the physical support conditions of an actual edge-type train; the chosen F_t local witness still has to be identified with this interface.
- TrainCoverageFreeBoundsFromMixed.lean derives auxiliary q-1 mixed forests when q>2, ordinary q-core support girth, and the genuine q=2 universal TOP FullSystemGirthGT 2 witness from ONE finite F_t mixed-SET forest through the SAME q. It does NOT falsely infer bottom local FullSystemGirthGT 2.
- TrainCoverageFreeForestOrderStep.lean applies the independently developed bottom original-B-labelled forest preservation to obtain FULL output bottom system girth q, then builds the coverage-free OrderStage and literal selected PictureStep using the F_t PHYSICAL A-edge Ramsey arrow. No ambient edge pruning or selected-copy relabelling.
- TrainCoverageFreePositiveTransfer.lean ports the checked exact positive proper-cut FullSystemGirthGT transfer, which likewise ignores mixedCoverage, into the weaker stage. No numerical cutoff is weakened.
- TrainCoverageFreeNontrivialFtStep.lean combines the TRUE two-edge induced active fibre, vector-admissibility inequalities, SAME-q F_t forest, positive local full bounds and train/part geometry into an actual coverage-free selected OrderStage PictureStep.
- TrainCoverageFreePhysicalFibre.lean ports the checked identity PictureStep for empty/singleton physical fibres and its nontrivial-fibre dispatcher. The singleton case makes no invented one-edge local attachment.
- TrainCoverageFreeStrongFinitePass.lean combines the coverage-free finite Ramsey pass with that dispatcher: only genuine nontrivial physical fibres call F_t, the rest are identity steps, and bottom girth + selected base lifts remain valid. The output is a selected A-strong B-copy preserving AND reflecting ALL original train relations at the SAME q::tail cutoff vector.

## Actual F_t witness integration still to check

The mathematical structural reduction is now explicit and drops the invalid coverage hypothesis, but unconditional F_t=>R_t remains **unverified**. The next integration must show that each selected local F_t witness for the TRUE induced active train provides:

- a finite P-partite local core over the old base D after actual A-part relabelling, with nonempty/vertex-covering physical A-support;
- one selected image per actual complete support and A-strong selected embeddings;
- a genuine finite mixed-SET forest through q (not duplicate labelled supports);
- exact all-cut part/train restriction of physical A-edges, including shared-wagon source/reflection and the universal top;
- adjacent part/intersection parameters after fine-part coarsening;
- full system girth at each proper positive cutoff h_i (not merely order-one bounds);
- the literal PHYSICAL A-edge Ramsey-arrow on the selected family (the checked indexed partite-arrow-to-physical-arrow theorem supplies the ordered-source bridge).

For q>=3, the checked true-active selected lower-stage bundles already support these inputs but are stronger than F_t; for q=2 they cannot simply provide an arbitrary F_2 witness's mixedCoverage. The new coverage-free constructor makes that stronger field unnecessary, but the actual partite local F_t output must still be connected to it.

## Validation and negative claims

1. **NO local Lean toolchain or compatible pinned partite-construction/lean-successors dependency cache in the active runtime.** No exact-head lake/Lean proof compilation, no #print axioms execution, no paid GitHub CI.
2. Static source checks cover imports, new-file import cycles, textual proof holes and checker registrations. They are NOT logical verification. The original finite-pass proof and bottom increment were ported without substantive proof changes, but Lean must check the new dependent stage types.
3. The q=2 local total A-core-coverage argument is demonstrably false in general; no stronger local mixed coverage is attributed to F_2. The q=2 universal-top cutoff-two theorem proves a DIFFERENT auxiliary field and does not repair that false inference.
4. Manuscript prop:globalize and preservation/cor:coordinate validation markers stay OPEN. The q=2 coverage gap is noted inside the EXISTING manuscript OPEN marker.
5. No appendix claims are included.

Suggested exact-head kernel sequence (once matching offline dependencies are available): compile TrainCoverageFreeForestStage, TrainCoverageFreeFinitePass, TrainCoverageFreeOrderPass, TrainCoverageFreeBottomIncrement, TrainCoverageFreeAttachment, TrainCoverageFreeBoundsFromMixed, TrainCoverageFreeForestOrderStep, TrainCoverageFreePositiveTransfer, TrainCoverageFreeNontrivialFtStep, TrainCoverageFreePhysicalFibre, TrainCoverageFreeStrongFinitePass, then CheckTrack4MinimumOwnerSwap.lean and inspect every printed axiom dependency.
