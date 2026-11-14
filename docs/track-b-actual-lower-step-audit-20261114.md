# Track B — exact lower selected stage to nontrivial refining PictureStep (14 Nov 2026)

## Scope and source of truth

Lean PR #1066 (replacement for the overlapping, failing PR #1051); the circulation manuscript is frozen. This note audits the conditional theorem
`ForestTailStage.refiningPictureStep_of_actualLowerSelectedStage` in
`Girth/TrainRecursiveActualLowerRefiningStep.lean`, and **does not certify it as Lean-compiled**.

The current exact-head candidate imports the merged mainline modules
`TrainRecursiveActualAttachedPositive`, `TrainRecursiveSelectedFineTrainHeight`,
`TrainRecursiveCanonicalFineParametersCast`, `TrainRecursiveFineWitnessStep`,
`TrainRecursiveTrueActiveIndexedNontrivialInputs`,
`TrainRecursiveActualHeightCutoffApplication`, and
`TrainRecursiveCanonicalFineAllowed`. The checker
`CheckTrainRecursiveActualLowerRefiningStep.lean` invokes `#print axioms` and is
registered in `scripts/check_track_d.sh`.

## Conditional construction: field-level audit

The genuine old stage is over `q :: tail` with `2 < q`. The true physical
active subsystem is cut out using the selected copy `e` and the actual
`FirstWagonRefinement R`. Define
`lowerCuts = replicate (R.extraCuts + 1) (q - 1) ++ tail`.
The exact equality
`lowerCuts.length = (q :: tail).length + R.extraCuts` transports the true
fine train and permitted A-parts, with inverse cast used **only** to present
the lower stage at its literal cutoff length.

The selected lower `ForestTailStage`, its literal designated-copy subtype
`I`, and `DesignatedArrow lower κ` are *premises*; they are NOT inferred
from a colour arrow on an artificial quotient or from a PictureStep at the
current rank.

- The ordered true-active indexed-input theorem derives actual
  two-copy geometry, `E.IsPartiteOver A`, irreducible A-coverage,
  physical injectivity, mixed-forest control, full target restriction,
  adjacent parameters and the indexed selected family arrow.
- The local `Finite I` instance uses physical injectivity into actual
  finite witness embeddings (avoid silently treating a set of selected
  indices as finite without proof). Check the function-space codomain
  instance during Lean elaboration.
- The lower selected stage's target restriction is transported
  two-way across `Fin.cast`; the fine adjacency parameters are transported
  with the **reverse** length cast and a separately proven inverse index
  identity. Check that `hAllowedIndex` elaborates exactly as written.
- The canonical refinement supplies the singleton, first-parent and
  positive retained permitted-set clauses, without fresh free premises.
- Genuine lower `FullSystemGirthGT` supplies q−1 bounds for inserted
  interior cuts and q for original interior cuts. Original positive-tail
  `SupremeCycleBound (t.get j)` comes from real refined-lower train
  reflection plus retained girth. None of these output certificates is a
  theorem hypothesis.
- The final call to `refiningPictureStep_of_fineWitness` must use the same
  literal `I`, `f`, `T`, and true active subsystem throughout.

## Historical errors and current exact-head obligations

Historical #1051 exact-head focused run 43202917683 failed at source lines
207/209: unsynthesized `Finite I` and `Unknown identifier hPair` after
destructive pattern elimination. The #1066 source repairs this with
`Finite.of_injective` and `Classical.choose hPair`, but that source
inspection is not a successful Lean kernel check.

**Required gates for this exact head**: complete Lean build; focused
`scripts/check_track_d.sh`; exact `#print axioms` output demonstrating
no `sorryAx`/untrusted axiom; regression scripts. Check the failing
diagnostics specifically for `Finite I`, `hAllowedIndex`,
`hParameters`, `hTail` and application of the final fine-witness theorem.

## Outstanding mathematical proof obligations (not supplied by this PR)

1. Construct a genuine selected lower-rank Ramsey `ForestTailStage` for
   `lowerCuts`, over a sufficiently large actual A-partite base, and
   establish `DesignatedArrow lower κ` via the well-founded recursion.
   An initial lower stage alone does not supply the Ramsey arrow.
2. Supply legitimate base geometry and the actual first-wagon refinement
   from preceding hypotheses. In particular `hTargetTwo` is explicitly
   retained and is **not** silently derived from projected `hPair`.
3. Finish the cutoff-two and absent/trivial-fibre branches; assemble a
   concrete `Operators.largerCutoff` and the other operator cases, rather
   than treating the generic `Operators.assemble` as existence.
4. Establish the full same-vector forest-to-order conversion before
   claiming the circulation forest lemma. Keep manuscript validation marks
   conditional on exact theorem and exact-head proof checks.

This note is only an auditable proof-dependency/CI record. It makes no
change to the manuscript, its validation markers, or the theorem statement.
