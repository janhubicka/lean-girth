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


## Final nontrivial-profile interface refinement (14 November)

- TrainActualFtNontrivialLocalStep.lean: ForestTailStage.orderPictureStep_of_nontrivial_Ft explicitly composes the genuine local same-q mixed forest with the checked source and positive tail transfers. It CONSTRUCTS ActiveAttachmentBounds, including its q-1 forest, core girth, cutoff-two top witness and tailSupreme, instead of accepting those as opaque local oracles. It requests the actual partite source, irreducible completion, selected image injectivity, train reflection, parameters, positive local full bounds and physical edge-colouring Ramsey arrow. The numeric 2<=t_i inequalities are explicit consequences of admissibility and are NOT derived from a girth bound.
- TrainForestStageCoveredNontrivialPass.lean: the checked ordered nontrivial-fibre dispatcher combines identity steps on subsingleton physical fibres with actual selected OrderStage attachments on nontrivial fibres. BottomReady and CoversBase are transported; the final selected strong train Ramsey arrow requires only one nontrivial-fibre local step operator.
- TrainForestStageTrueActiveSameVectorGirth.lean: bottom FullSystemGirthGT q plus the retained old positive tail bounds imply the exact labelled wagon-girth vector q::tail in the honest induced active train. This applies F_t using inherited WAGON girth, never a false full-system-girth assertion about the active subsystem.
- TrainForestStageFtEligibleFinitePass.lean: the full conditional finite selected Ramsey pass only asks for a local F_t operator on nontrivial active fibres satisfying the exact inherited labelled wagon girth at the SAME vector; all other readiness, identity-fibre, strong-train extraction and coordinate bookkeeping is composed from existing libraries.
- The full unconditional mathematical F_t=>R_t assertion STILL requires showing that F_t's actual witness has the stated partite / irreducible-coverage / selected-image / exact positive-cut / physical-arrow fields and that those local outputs are valid for every profile. These are not kernel certified.


## 15 November: selected F_t witness is already an indexed physical local witness

The existing checked modules TrainRecursiveSelectedWitnessConsequences.lean, TrainRecursiveCoarsenedSelectedIndexedBundle.lean and TrainRecursiveActualCoarsenedFullSystem.lean already derive the actual selected local F_t data from one genuinely selected lower ForestTailStage, conditional on the correct true-active source and part-preserving large base:

- E is A-partite and has irreducible-to-A coverage.
- Its genuine selected gluing labels have injective COMPLETE A-support pieces (the stage's selectedPhysicalInjective field), and its finite mixed support forest is valid through the requested q.
- All cut train relations on selected images are reflected, core adjacent parameters are retained and the indexed selected partite Ramsey arrow is available.
- At every positive local cut, the selected gluing witness inherits the exact original FullSystemGirthGT threshold from the REAL lower ForestTailStage.tailGirth, not a new lower oracle.

**New short adapters**:
- bSupportPiece_eq_of_same_carrier and activeGluingWitness_distinct_images_of_supportPiece_injective show that injective COMPLETE support pieces imply injective vertex images: equal carriers force equal full edge sets. Conversely, image injectivity implies support-piece injectivity by reading the piece carrier. The new nontrivial local step now accepts selected SUPPORT injectivity directly, matching the checked lower-stage output.
- TrainIndexedPartitePhysicalArrow.lean: the checked selected INDEXED partite A-arrow yields a PHYSICAL A-edge arrow, because every relational A-copy in an A-partite source is partite when finite ordered A is rigid. No new selected index, extra colours or arbitrary embedding-arrow hypothesis.
- TrainRealSelectedFtLocalBundle.lean: the checked indexed lower bundle plus that physical-arrow adapter yields all seven local geometry/forest/train/parameter/physical-arrow fields; its trueActive_sameVector_localBundle_with_positive theorem also includes the exact positive-cut FullSystemGirthGT bounds from coarsenedSelected_fullSystem_at_positive. This reduces the previously separate local witness assumptions to the genuine EXISTENCE of a selected F_t ForestTailStage and its exact true-active/coarsening presentation.

**Last compatibility work** (no false completion claim):
1. Identify the genuine lower target train with the old stage's exact twice-restricted active train, and convert the checked selected train relation to the full shared-edge interior compatibility interface. Preserve the literal physical support labels and old/core wagon embeddings.
2. Check the actual A-part relabelling of the lower partite witness into the P-partite attachment, including all allowed-part parameters and the indexed selected physical arrow (rather than an unindexed abstract arrow).
3. Verify the true-active target has irreducible-to-A coverage at q=2 as well as q>2, and supply the finite F_t stage and its selected DesignatedArrow for every ordered nontrivial fibre.
4. Run the exact-head Lean kernel checker before promoting any manuscript validation markers. No compatible offline toolchain/dependency bundle is mounted; no new CI run was started.

## Critical 15 Nov q=2 core-coverage gate

See [track-4-q2-core-coverage-obstruction-20261115.md](./track-4-q2-core-coverage-obstruction-20261115.md). The q>=3 active-source extension theorem uses support girth >3 and cannot be invoked when head cutoff q=2. An explicit K4-partite, A-generated graph with physical support girth >2 has a mixed irreducible K3 not contained in any K4 copy. Thus `ActiveAttachmentBounds.coreCoverage` is not a consequence of the same-q=2 mixed forest, A-linearity and partiteness alone. The new universal-top FullSystemGirthGT 2 proof only supplies the *different* `cutoffTwo` field; it does not solve `coreCoverage`. In the q=2 finite conversion either construct a weaker q=2 attachment preserving the required mixed A-or-B output coverage, or use a separate base-case picture-step. Do NOT declare unconditional F_2=>R_2 complete from current modules. No status marks were changed.
