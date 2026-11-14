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

## 14 November continuation (new conditional endpoints)

- `TrainRecursiveRefinementDoubleGirth.lean` now treats the **bottom equality cut** separately with the existing noninjectivity lemma. Its displayed argument does not *use* the record's bottom child-girth field. The record still contains that field; hence this is **not** a theorem with a genuinely weakened input structure, and it must not be advertised as such.
- Added `FirstWagonRefinement.actualSupport_girthGT_of_first_universal_twice` for true A-support with an explicitly universal first wagon.
- Added `Girth/TrainRecursivePhysicalFineGirthDouble.lean`, with two conditional endpoints: `selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts` derives true physical A-support girth `> min(2*g+1,h)` from the same named fine bottom/positive system bounds, genuine parent parameters, and retained actual first full-system cutoff `h`; `selectedPicture_actualSupport_girthGain_twice_of_firstUniversal` gives the empty-tail `>2*g+1` under explicit first-universality. Neither constructs the selected lower witness or output stage.
- Extended the manuscript-branch finite test: besides all sharp `2g+2` examples for `2<=g<=20`, it now checks **every** smaller retained-tail cutoff `g+1 <= h <= 2g` for `2<=g<=16`, building an `h+1`-cycle of singleton first wagons with valid part assignments. All local Python tests passed.
- As of this audit, upstream `girth/main` has moved to `6e2048b7cbc6d16c27dfcdaf8e67924f5906f846` with unrelated changes; the manuscript branch has no overlapping changed paths but is intentionally not merged. `lean-girth/main` has moved to `b0b3c49a7d2b47150f146df588b5868be9d6cce3` with documentation and workflow changes.
- An offline local Lean installation using the *historically verified* 8 Nov GitHub Actions artifacts was investigated. The original nine artifacts are no longer listed on workflow run `42512209025` (expired); the container has no installed Lean, Lake, or mathlib and cannot resolve GitHub. **No Lean elaboration or axiom audit occurred**. No replacement Actions runs were triggered.
- Source-level inspection confirmed pinned Mathlib defines `finRotate : ∀ n, Equiv.Perm (Fin n)` and `Fintype.card_bool`, which are used by the candidate; this is API inspection, not a compilation result.

**Next exact-head gate:** compile `DoubleCount`, `DoubleStep`, `DoubleGirth`, `PhysicalFineGirthDouble` in order and run their printed axioms before changing any manuscript validation marker. Reuse all existing `g+1` certificates without waiting for the stronger estimate.
