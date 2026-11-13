# Numbered Track 7 — exact indexed recursive-witness audit (13 November 2026)

## Scope and certificate policy

- Manuscript target: \`janhubicka/girth@8c9cfa6eb6d817a08f3009fe048fc0be07426ece\` (merged PR #445), source digest \`45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec\`. The explanatory-only manuscript branch is draft PR #446 and is **not** a new validated baseline.
- Work queue: #1058; programme #1060; Lean setup baseline \`e57c954c6417604d35332adfdf3304a225281eca\`.
- This is a source-level declaration/interface audit. The checker files listed below contain \`#print axioms\` commands, but no new Lean invocation, output, or \`#print axioms\` result is asserted here. Historical CI does not promote the revised manuscript's theorem markers.
- Goal: an **unconditional** realization of \`FF_t\` for every admissible nonempty monotone cutoff vector, followed by \`RR_t\` at the **same** vector and the height-one local-forest extraction. The constructive statement must quantify over the real ordered target, colour type, prescribed parts, parameters and all ambient edges and wagons.

## Source-to-Lean integration map

| Obligation | Existing Lean entry point | Exact status |
| --- | --- | --- |
| Cutoff-count lexicographic induction, rank decreases and same-vector order conversion | \`TrainRecursiveWitness.lean\`: \`Operators.assembleBounded\`, \`Operators.assemble\`, \`Operators.assembleOrder\`; \`TrainCutoffWellFounded.lean\`, \`TrainCutoffLexRank.lean\` | Generic conditional recursion, not instantiation of any geometry |
| Genuine fine target and all lower cut indices for \`q>2\` | \`TrainRecursiveTrueActiveLowerCutoffVector.lean\`: \`trueActive_inducedAllLowerCutGirth\`; \`TrainRecursiveTrueActiveFineParameters.lean\`: \`trueActive_inducedRefinementAdjacentParameters\` | Input geometry derived from real old stage and supplied true refinement \`R\` |
| Base for lower induction | \`TrainRecursiveTrueActiveHJInitialNoTargetAssumptions.lean\`: \`exists_initialLowerStage_over_strongHJBase_from_refinement\` | Constructs actual *initial* lower stage and HJ family arrow; **not** the completed selected lower \`DesignatedArrow\` |
| Complete lower finite pass | \`TrainRecursiveHJFreshSelectedFinitePass.lean\`: \`constructFromPartiteTargetCuts_of_freshNontrivialRefiningSteps\` | Conditional on fresh nontrivial local \`actualStep\`; no self-supplying lower-stage operator |
| Literal indexed selected family | \`TrainRecursiveCoarsenedSelectedFamilyArrow.lean\`: \`selectedPartiteFamilyArrow_after_coarsen_of_designatedRelationalArrow\` and \`ForestTailStage.selectedFamilyArrow_after_largeBaseCoarsen\`; \`TrainRecursiveCoarsenedSelectedIndexedBundle.lean\` | Correct selected subtype, conditional on a *real* lower \`ForestTailStage\` with \`DesignatedArrow\` and part-preserving base family |
| Physical local input, including nontriviality | \`TrainRecursiveTrueActiveIndexedNontrivialInputs.lean\`: \`ForestTailStage.orderedTrueActiveSelected_indexedInputAndTwoCopies_of_nontrivial\` | Derives the seven local inputs and the two actual A-copies, still conditional on that lower stage |
| Complete fine interior system girth | \`TrainRecursiveActualCoarsenedFullRecursiveCutoffs.lean\`: \`ForestTailStage.coarsenedSelected_fullSystem_for_recursiveCuts\`, \`...for_attachmentHeight\` | Derives physical \`hFull\` from lower \`tailGirth\`: \`q-1\` on inserted cuts, \`q\` on retained interior cuts |
| **Exact** original positive tail bounds | \`TrainRecursiveActualRetainedSelectedWitnessGirth.lean\`: \`ForestTailStage.coarsenedSelected_retainedSharedFullSystem_of_realStage\` | Derives lower *shared witness* \`FullSystemGirthGT (t.get j)\`, including nonconstant original tail thresholds, from real lower stage |
| **Attached output** tail supremeness | \`TrainRecursiveIntrinsicTailSupreme.lean\`: \`ForestTailStage.attachedAllPositiveSupreme_of_intrinsicWitness\` | Derives attached output \`SupremeCycleBound (t.get j)\` from old \`tailGirth\`, shared lower girth and additional **actual** \`hRel\`, \`hStrong\`, base linearity/rigidity, two-copy conditions. These interfaces are not yet a single theorem that automatically supplies the \`hTail\` argument of the next row |
| Individual genuine picture step | \`TrainRecursiveFineWitnessStep.lean\`: \`ForestTailStage.refiningPictureStep_of_fineWitness\` | Builds next stage, but still takes the actual fine witness, **indexed** \`hArrow\`, complete fine \`hFull\` and attached output \`hTail\` as hypotheses |
| Fresh finite pass/final designated family arrow | \`TrainRecursiveFreshRefinementPass.lean\`: \`constructFromTargetCuts_of_freshNontrivialRefiningSteps\` | Handles freshness, empty or trivial fibres, backwards Ramsey selection; still requires every nontrivial \`actualStep\` |

Relevant checker source files with \`#print axioms\`: \`CheckTrainRecursiveWitness.lean\`, \`CheckTrainRecursiveFineWitnessStep.lean\`, \`CheckTrainRecursiveCoarsenedSelectedFamilyArrow.lean\`, \`CheckTrainRecursiveCoarsenedSelectedIndexedBundle.lean\`, \`CheckTrainRecursiveActualRetainedSelectedWitnessGirth.lean\`, \`CheckTrainRecursiveIntrinsicTailSupreme.lean\`, \`CheckTrainRecursiveHJFreshSelectedFinitePass.lean\`, \`CheckTrainRecursiveTrueActiveHJInitialNoTargetAssumptions.lean\`. Presence of a gate **does not imply its output was run or checked in this audit**.

## Correct induction and the remaining noncircular construction

Let \`t = q :: tail\`, with \`q>2\`, and let a nontrivial active profile have true depth \`d=R.extraCuts+1 >= 1\`. The recursive request is

\`\`\`text
lower = replicate d (q - 1) ++ tail
\`\`\`

This has strictly smaller cutoff-count lexicographic rank at the original ceiling. Invoke the universal lower-rank \`ForestWitness lower\` on the **entire** genuine refined active target, including all its inherited and inserted relations, with its actual selected part-preserving family. A lower witness must deliver a selected \`DesignatedArrow\` and every \`FullSystemGirthGT\` coordinate, *not* only an initial HJ stage or unindexed \`Partite.Arrow\`.

Use the **larger-base** selected coarsening, not a fictitious base on the vertex type of \`A\`: \`TrainRecursiveActiveTargetNoSmallBase.lean\` proves that the genuine nontrivial source cannot inject into an A-sized base. Composing part maps preserves the same selected indexed embeddings and the complete physical edge/wagon family. The exact lower positive cut bounds give \`hFull\` at \`q-1/q\` via \`...for_recursiveCuts\`, and the stronger original retained \`t[j]\` via \`...retainedSharedFullSystem_of_realStage\`. Feed the latter into \`...attachedAllPositiveSupreme_of_intrinsicWitness\` to produce the needed output \`hTail\` **after discharging its actual old-base/selected restriction hypotheses**. Only then apply \`refiningPictureStep_of_fineWitness\`, giving the genuine \`actualStep\` for the original-rank finite pass. No lower stage at the **current** rank may be supplied as a premise.

For \`q=2, tail ≠ []\`, instantiate \`RR_tail\` by first building \`FF_tail\` at smaller rank and converting it; obtain the actual parent-indexed cutoff-two realization and its selected family through Track 5. \`t=[2]\` needs the genuine covered base from Track 1. Finish the original-rank fresh pass and instantiate the concrete \`Operators\` record; after \`FF_t\`, call \`forestToOrder\` exactly once at that same vector.

## Outstanding integration gates (not certified)

1. Define concrete \`ForestWitness\` and \`OrderWitness\` predicates (including all target/colour/part and literal family quantifiers), and instantiate \`Operators.baseTwo\`, \`cutoffTwo\`, \`largerCutoff\` and \`forestToOrder\` with genuine witnesses rather than construction operators as assumptions. The lower finite pass must be invoked through a strictly smaller-rank witness; the apparently tempting direct use of \`constructFromPartiteTargetCuts_of_freshNontrivialRefiningSteps\` at current rank would be circular.
2. Build a single \`q>2\` nontrivial-step theorem that obtains lower indexed \`DesignatedArrow\`, \`hFull\` and **derived \`hTail\`** from the universal lower witness. Explicitly verify the \`hRel\` for *every* relevant cut and the \`hStrong\` condition on the entire designated base family, not just currently selected images, along with true physical support coverage, ordered rigidity and type/height casts. These are not implied by \`TrainRecursiveFineWitnessStep\` by itself.
3. Obtain the genuinely selected parent-indexed cutoff-two realization/arrow and all positive proper cuts (Track 5). Retain original parameters and ambient edges. The weaker old refinement \`g+1\` is sufficient for recursion; the 2g+1 strengthening is not a prerequisite.
4. Complete same-vector forest-to-order conversion with both cycle-preservation alternatives, then height-one extraction with isolated vertices restored privately only at the end (Track 8).
5. Once all four fields and the final theorem elaborate, run an **exact-head local Lean build**, capture actual \`#print axioms\` output (no \`sorryAx\`/unapproved axioms), check finite regression cases, and only then update manuscript validation markers. EHN is an approved explicit external input, not an unmentioned constructor.

## Editorial outcome

Draft manuscript PR [#446](https://github.com/janhubicka/girth/pull/446) adds a short explanation of literal selected-index coarsening before the recursive proof and clarifies that the lower induction is applied to the whole refined active subsystem; it does not change any numbered theorem or claim new validation. The changes were statically audited against two exact TeX blobs (same label, marker and environment counts); no local TeX/Lean kernel build was available in this session.
