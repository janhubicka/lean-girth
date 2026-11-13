# Track 6 — doubling candidate and exact validation gate

**Uncompiled. Do not promote any manuscript validation marker.** No paid Actions were requested.

Frozen manuscript baseline: `girth/main@8c9cfa6e`, source digest `45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec`.
Working English proof: `girth/revision/track6-refinement-proof-clarity-20261113@22c27a89` (different source digest).
Lean branch base: `lean-girth/main@4d102cae`.

## Exact theorem interfaces

- `TrainRecursiveRefinementDoubleCount.lean`: `card_double_le_of_two_preimages` — pure finite injection, no geometric inputs.
- `TrainRecursiveRefinementDoubleStep.lean`: `child_has_second_occurrence_of_singleton_intersections` and `child_constant_of_singleton_intersections_twice` — requires transversality, singleton-part sibling intersections, complete labelled child girth >g.
- `TrainRecursiveRefinementDoubleGirth.lean`: `girthGT_firstWagon_twice`, `girthGT_of_first_universal_twice`, `girthGT_of_retainedFirstCut_twice`, `actualSupport_girthGT_of_retainedFirstCut_twice` — iterated local descent, universal empty-tail case, retained-cut cap `min (2*g+1) h`, actual A-support specialization.

## Local certification commands (NOT YET EXECUTED)

```bash
lake env lean Girth/TrainRecursiveRefinementDoubleCount.lean
lake env lean Girth/TrainRecursiveRefinementDoubleStep.lean
lake env lean Girth/TrainRecursiveRefinementDoubleGirth.lean
```

Each file prints endpoint axioms. Check output for `sorryAx`, unintended axioms, and elaborated assumptions. Do not treat presence of source-level proofs as kernel validation.

## End-to-end limits

Existing older `g+1` conditional adapter remains independent and sufficient for the recursion. The new doubling estimate must not replace the q-1 mixed-forest induction.
Missing from this candidate: actual fine selected witness, original-tail full-system bounds, selected Ramsey arrow and strong embeddings, and fresh-cut output-tail preservation. These require Track 3/4 and Track 7 integration.

Adversarial boundaries: classes may reappear nonadjacently; the local `2g+2` sharp example requires depth two; nonempty-tail global doubling is false for `g=2,h1=3` (four-cycle); parent-local child girth does not imply global retained first-cut girth.

Bounded Python diagnostic (not Lean): 142,416 set-partition words through length 10; all checks passed.