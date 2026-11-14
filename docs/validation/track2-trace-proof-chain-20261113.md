# Numbered Track 2: proof chain and remaining validation gates

Status: **source-level candidate, not kernel-verified** (updated 14 November 2026).

## Exact sources and separation of branches

- Frozen circulation reference: `janhubicka/girth/main@8c9cfa6eb6d817a08f3009fe048fc0be07426ece`, reachable-source digest `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
- Unmerged current paper edits: [`edit/track2-current-proof-20261114`](https://github.com/janhubicka/girth/tree/edit/track2-current-proof-20261114), based on `girth/main@61b5a511ceb7bf4bb483ccdcf564306af23b7dc6`; this preserves the independently rewritten cutoff-three proof. The frozen reference is not modified.
- Unmerged Lean candidate: [`validation/2-forest-trace-rebased-20261114`](https://github.com/janhubicka/lean-girth/tree/validation/2-forest-trace-rebased-20261114), based on `lean-girth/main@b0b3c49a7d2b47150f146df588b5868be9d6cce3`. The previous `98e40142` source candidate is preserved on its historical branch; this branch contains its checked-for-overlap source files and newer interface adapters.
- No paid GitHub Actions checks launched. This checkout did **not** run Lean; local compiler/mathlib binaries are unavailable. The exact candidate `#print axioms` commands are in `Girth/CheckTrack2Trace.lean`, but have not been executed.

## Exact theorem chain

| Manuscript role | Candidate / existing Lean source | Contract |
| --- | --- | --- |
| `lem:foresttracegirth` | `ForestTraceAcyclic.girthGT_union_of_forest_edge_traces`, `girthGT_selected_of_forest_edge_traces` | Linear H, edges of size ≥2, every member traces at most one H-edge, selected edges occur as whole traces. Uses checked `girthGT_union_of_forest`; avoids another leaf induction. |
| Indexed finite Berge-cycle contradiction | `ForestActiveTraceGirth.girthGT_of_bounded_smallOrWhole_forest_completions` | Turn a cycle into an injectively indexed family of mandatory edges; complete it, then pull back acyclicity. |
| **Actual forest completion → active girth** | `ForestCompletionTraceBridge.girthGT_of_forestCompletion_designated_traces` | Consume the existing `ForestCompletionProperty` and `ForestCompletionWitness` records. Selected A-edges lie wholly inside S; require the boundary classification only for *added designated B-members*. The earlier stronger all-tested-piece version was removed. |
| Actual selected B boundary | `ForestActiveTraceBoundary.projectedBCopy_smallOrWhole_activeBoundary` | The existing `projectedCopy_activeCarrier_intersection_classify` plus actual membership in the B-member's own A-support, not merely carrier intersection. |
| True **old** active subsystem girth | `ForestOldActiveGirth.oldActiveSupport_girthGT_of_designatedCompletion`, `oldActiveInduced_girthGT_of_designatedCompletion` | Exact designated A/B piece predicates; old A-linearity, base B-projection A-strongness, genuine finite completion, two distinct vertices of A. Recover the actual induced active support via the existing mapped-support equivalence. Does **not** assume processed-output girth. |
| Structural step already implemented conditionally | `ForestStructuralABCompletion.assemble_actual_AB_from_local_copy_cover` | Reuse the old completed picture and an actual local witness with A-copy coverage, local forest bound and output A-linearity. The generic join-tree lemma's singleton-helper refinement is **not** needed to apply this theorem to the edge-covered structural construction. |
| Direct increment | `ForestActualRecursiveIncrement.actualPartiteDesignatedAB_mixedForest_of_relationalLocal` | A local witness, q=2 base versus q≥3 predecessor, whole gluing-image strongness, and independent output A-linearity/girth two. Do not derive the ambient girth assumption circularly from the desired forest. |

## Adversarial audit conclusions

1. The active-girth conclusion is about the *old* induced subsystem `(C.induce S).toRelStructure`, not `ProcessedActiveGirth.processed_activeSubsystem_girthGT_of_local`, which concerns the *new processed* subsystem.
2. The image edge set `H` must be exactly `mappedSupportCopies A (C.induce S) C incl`, rather than all ambient A-support edges or an arbitrary set of labelled edge occurrences. The endpoint constructs its containment, image-membership and reflection proof.
3. A designated B-copy's boundary must be a genuine complete A-support edge of that B-piece. The existing factorization `bSupportPiece_eq_embeddedACopySupportPiece` supplies this.
4. For the **general** `lem:joinlift`, `forestOfCopies_lift_local_of_linear` is too strong on singleton separators. The generic helper adapter can attach one temporary singleton per *oriented singleton link* **after** local completion, without entering the completion budget. Per-vertex deduplication is unnecessary. The checked `selectedForest_of_distinctOwnerRequestImages` and short auxiliary deletion are reuse candidates. This general proof is independent of the structural theorem's edge-covered use.
5. Retain requests that are also selected or added local-completion members. Deleting such members would change the claimed result. No arbitrary-subfamily heredity is available.
6. There is **no new kernel certification yet**: a well-typed-looking Lean source candidate, a text audit and finite diagnostics cannot establish that Lean elaborates the statements or that `#print axioms` is clean.

## Exact completion gates

From a checkout of this candidate branch with the pinned toolchain and mathlib cache:

```bash
LEAN_NUM_THREADS=1 lake build Girth.CheckTrack2Trace
lake env lean Girth/CheckTrack2Trace.lean
```

After a successful compilation, inspect the printed assumptions of every new theorem, reject `sorryAx` and unapproved axioms, and record source commit and exact imported declarations. Then prove the remaining exact **manuscript forest-extension ↔ typed support completion** adapter; check both its nonempty and empty finite-selection cases. Only then promote a validation marker for `lem:puresubsystem`. The separate general `lem:joinlift` and end-to-end `prop:certpres` remain open.

## Reproducible finite tests

The paper branch's `validation/numbered-tracks/check_trace_and_singleton.py` covers triangles and squares with 0–2 auxiliary member carriers; the negative square test was independently executed locally with 667 configurations and all possible labelled trees. It is a bounded counterexample diagnostic, not a general proof.

## 14 November continuation: source-level repairs

- The original cycle argument passed `Fin c.length : Type 0` to a
  `ForestCompletionProperty` indexed in `Type v`. The revised
  `girthGT_of_bounded_trace_forest_completions` instead uses the finite
  subtype `{e : Set W // e ∈ Set.range c.edge} : Type v`.
  The surjection from `Fin c.length` to that subtype proves
  the cardinal bound, while `Subtype.val` injectivity distinguishes
  physical cycle edges. The relevant Mathlib
  `Fintype.card_le_of_surjective` API was checked in public Mathlib
  source; **Lean elaboration of this candidate was not run**.
- `Girth/ForestFiniteSetCompletion.lean` now defines
  `FinsetForestCompletionProperty` and its
  `FinsetForestCompletionProperty.toIndexed` theorem.
  Its proof takes the image of an arbitrary finite indexed
  selection and uses `Finset.card_image_le` to control
  repetitions without an injectivity assumption.
- `Girth/ForestOldActiveSetGirth.lean` gives the
  `oldActiveInduced_girthGT_of_supportFinsetCompletion`
  endpoint, invoking the preceding finite-set adapter
  and the existing `oldActiveInduced_girthGT_of_designatedCompletion`.
  This is a precise **support-set** interface, not yet an
  identification of actual relational copies with their support pieces.
- Removed the unused generic A-strong one-edge-boundary lemma
  from `ForestActiveTraceBoundary.lean`. Only the
  projected-designated-B boundary statement is needed:
  the selected A-edges already lie inside the old active subsystem.
- The paper edits were copied onto the **current editorial main**
  in [`edit/track2-forest-trace-rebased-20261114`](https://github.com/janhubicka/girth/tree/edit/track2-forest-trace-rebased-20261114);
  this preserves parallel Track 3, 7 and 8 changes. The old
  41-page digest is the frozen baseline, not the digest of
  the new branch. The English proof of `lem:foresttracegirth`
  was shortened to the same trace-piece/forest-union argument
  used by the Lean candidate.

The exact source and axiom gate still need a focused, **real**
Lean compilation with pinned dependencies. The source edits
are not evidence of a successful kernel check. Do not upgrade
validation markers yet.


## 14 November — actual copy-set interface closed as a conditional theorem

The candidate now adds two direct **source-level formal adapters**.

- `Girth/ForestCopySetCompletion.lean` defines
  `FinsetLabelForestCompletionProperty` for finite SETS of labels of
  actual copies, measured using the **complete support-piece** forest.
  Its `toSupportIndexed` theorem takes any finite indexed family of
  selected support pieces, chooses a genuine copy label for each
  tested support, takes the finite set of chosen labels, applies
  copy-set forest extension, and returns the existing
  `ForestCompletionProperty` with all selected pieces surviving
  and every extra member designated. The image cardinality is
  at most the original family size, and no support-map injectivity,
  arbitrary subfamily heredity, or fabricated output bound is used.
- The converse `FinsetForestCompletionProperty.toLabelFinset`
  turns any finite-support-set completion property into a
  copy-label-set completion property, again with no injectivity
  assumption on support. This isolates the two natural descriptions
  of the manuscript's finite-set condition.
- `Girth/ForestOldActiveSetGirth.lean` defines
  `pictureABLabelSupport` on the genuine sum type
  `Embedding A C ⊕ DesignatedCopy B D C family`, using a
  one-edge A-piece or the full B-support piece respectively.
  `testedPictureABSupport_iff_label` proves that the
  **tested support predicate is precisely the image of these
  actual labels**. Finally,
  `oldActiveInduced_girthGT_of_actualCopySets` derives the old
  active induced-subsystem girth directly from a finite-set
  forest-extension hypothesis on these labels. No injectivity
  of the support map is assumed.

This closes the **translation between finite actual-copy sets and
the existing typed support-completion invariant**, conditional on the
manuscript's mixed-forest extension hypothesis and the stated base
strongness/linearity assumptions. It does not construct the Ramsey
witness needed in other tracks and it does not certify the paper's
different general singleton-free join-tree statement.

The focused `Girth/CheckTrack2Trace.lean` now contains
`#check` and `#print axioms` probes for all new endpoints,
including the bidirectional set adapters. No local Lean toolchain or
pinned mathlib cache was found in the container; direct GitHub
egress failed DNS. Hence **no new kernel claim is made**, even
where a proof term contains no `sorry`.

The manuscript branch was synchronized again onto the current
source, preserving the separately revised `paper/07-forest-increment.tex`.
Only the independent output-linearity preface was transported into
that proof; the older Track 2 copy of that entire file was NOT
pushed, so the newer cutoff-three result is preserved.
