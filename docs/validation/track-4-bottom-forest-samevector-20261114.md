# Numbered Track 4 — cycle preservation and same-vector forest conversion

Status: **UNCOMPILED mathematical Lean source candidate**. This note describes the non-appendix circulation proof only. Do not promote manuscript validation marks or merge as verified.

## Pinned work

- Lean draft: [PR #1064](https://github.com/janhubicka/lean-girth/pull/1064), base main 98e40142f95cf818f498ed21faf9302a50fe7832
- Manuscript draft: [girth #448](https://github.com/janhubicka/girth/pull/448), circulation source 8c9cfa6eb6d817a08f3009fe048fc0be07426ece, reachable-source manifest SHA-256 45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec
- Validation queue: [issue #1055](https://github.com/janhubicka/lean-girth/issues/1055)

## Bottom one-step proof candidate

- Original source n=2: zero geometric cuts use the checked old one-standard transfer. Two distinct owners force the intersection of the ORIGINAL occurrence carriers into the attached core. A-strongness of the core and the small-or-whole selected B boundary turn this into a pairwise allowed support intersection; the existing bottom two-member lemma yields an ORIGINAL selected B-labelled global supreme plan. No full-system local witness girth is needed.
- Original source n>=3: reuse the checked mixed-short normalization, minimum genuine geometric owners, and source supreme pullback. Bottom actual boundary and core cut geometry exclude mixed singleton segments. Direct cyclic charging gives c_i+c_(i+1) <= w_i and hence 2*#cuts <= twiceOrder(C), avoiding explicit cyclic segmentation just for the budget. The literal witness reduct of length <=q is globally supreme from local forests, including n=2 without presupposing A1. Existing zero/two/three-plus-cut physical source transfers return a supreme ORIGINAL B-label. Bottom long pieces are impossible.
- Endpoint: TrainActualBottomFullSystemForestPreservation.lean derives actual FullSystemGirthGT q for all original source lengths, conditional on the genuine local mixed forest through q and the old selected picture bound.

## Honest F_t local data, same vector

- A local forest is a claim about FINITE SETS of distinct complete selected support pieces together with all ambient one-edge pieces. Arbitrarily duplicating a multi-edge support under two names is invalid. The one-image-per-selected-embedding condition in F_t gives the required support-piece injectivity because each complete support piece remembers its carrier.
- TrainActualWitnessBottomMixedForestBridge.lean and TrainActualBottomForestFromFiniteMixed.lean derive the indexed local forest, local A-linearity, local A-strong gluing images and actual bottom output FullSystemGirthGT q from the SAME finite mixed-forest cutoff q. No local full-system-girth witness is assumed at bottom.
- For q=2, mixed forests alone do NOT imply local bottom FullSystemGirthGT 2; an explicit six-cycle/induced-path counterexample is in [the cutoff-two note](./track-4-cutoff-two-top-20261114.md). At the universal TOP, all physical edges have one wagon parent; the new top classification proves local FullSystemGirthGT 2 structurally from A-linearity, copy vertex support and A-strongness. TrainActualCutoffTwoFromMixed.lean discharges the exact existential cutoffTwo witness at the top, not at the bottom.
- ActiveAttachmentBounds.of_sameVector_finiteMixed derives the auxiliary local q-1 forest, q-core girth and cutoff-two fields from one genuine local F_t forest through q. The remaining actual partite, coverage, selected-base, interior train, parameter and positive-cut data are explicitly supplied by F_t / old picture, never invented.
- TrainActualFtNontrivialLocalStep.lean derives output positive full-system bounds from the old stage's exact tailGirth and local positive F_t full-system bounds at their own cutoff, constructs the actual attachment bounds, and concludes a selected OrderStage PictureStep. It requires the vector inequalities 2<=t_i explicitly; no girth certificate is misused to infer numerical admissibility.

## Correct physical-fibre case split — crucial correction

- If the projected fibre has at most ONE physical A-copy carrier, use the already checked identity picture step in TrainRecursiveWitnessPass.lean / TrainRecursiveNontrivialFibre.lean. No local witness and no attachment is necessary. The original ForestTailStage, selected train relations, parameters and all girth bounds remain unchanged.
- Otherwise two distinct projected carriers give two actual distinct A-support edges inside the TRUE induced active subsystem, by the checked activeSupport_two_distinct_of_projected_carriers. Apply same-vector F_t to that nontrivial source.
- We deleted five newly drafted one-edge ATTACHMENT modules: their attempted nontrivial ActiveAttachmentBounds would be impossible at q>2, because that structure requires two distinct active source edges. The correct one-edge branch is IDENTITY, not a degenerate physical attachment.
- TrainPhysicalEdgeToEmbeddingArrow.lean identifies the F_t colouring of physical A-edges with the formal picture-step colouring of A-embeddings under carrier rigidity. This holds for finite ordered A via the previously checked ordered_embedding_eq_of_sameCopy. There is no stronger Ramsey assumption.

## Selected base coverage and the finite Ramsey pass

- Checked older source transfer lemmas request strongness of every prescribed base B-copy. ActiveAttachmentBounds alone only supplies this for SELECTED copies. TrainActualSelectedBaseCoverage.lean proves it for the whole prescribed family if every base copy has a selected lift (CoversBase).
- The disjoint initial picture has CoversBase by the checked initialPicture_lifts theorem. Each selected TransitionEmbedding and PictureStep preserves CoversBase. Thus the required finite readiness condition is BottomReady AND CoversBase, not just BottomReady.
- TrainInitialOrderStageFromTargetCuts.lean derives initial full system-girth at every proper cut from the TARGET labelled wagon girth, without extra initial ordinary/full girth assumptions. TrainInitialOrderStageSelectedCoverage.lean packages this with actual selected base coverage.
- TrainForestStageCoveredBottomReadyPass.lean composes the checked finite ramseyPass with concrete readiness, obtaining a final OrderStage and strong selected target-train monochromatic arrow, CONDITIONAL on a bottom-preserving PictureStep at each ordered profile.
- TrainActualSameVectorForestWithParameters.lean derives positive proper-cut bounds at each exact h_i and adjacent parent-intersection parameters, using the already checked intrinsic parameter theorem. The universal TOP is a parameter endpoint, not a further system-girth coordinate.

## Remaining REAL gates

1. Exact-head lake env lean CheckTrack4MinimumOwnerSwap.lean. Inspect printed axioms; repair elaboration/signature errors and independently audit the theorem hypotheses. **No matching local Lean/lake/elan and pinned dependency bundle in this runtime**; no CI requested.
2. Verify F_t supplies a real partite local train witness with physical selected arrow, one selected embedding per image, true active-girth inheritance, A-irreducible coverage, exact interior train relations, original part parameters and positive full system-girth at h_i. The nontrivial local adapter states these hypotheses explicitly.
3. Use the above genuine local witness in every nontrivial fibre, identity in every subsingleton fibre, and complete the full finite profile-pass readiness induction. Prove the final unconditional F_t=>R_t and fine-part/ordering/coarsening output. This is **not** certified yet.
4. No appendix validation, no merge, no promotion of manuscript OPEN markers before a kernel check.
