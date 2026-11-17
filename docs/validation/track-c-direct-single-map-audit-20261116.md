# Track C — direct single-map audit (16 November 2026)

## Source inspected

- `TrainFillingPrivateActualSingleMapAllCuts.lean`
- `TrainFillingPrivateActualSourceEdgeEquiv.lean`
- `TrainFillingPrivateActualChoiceTrain.lean`
- `TrainFillingPrivateActualTwoTypeTargetGirth.lean`
- `TrainFillingPrivateActualOrderAllCuts.lean`

**Verification:** this note is an adversarial source audit. None of the new Track 5 declarations is certified by the note; do not promote manuscript markers.

## A shorter proof path already exists

The direct construction `actualOriginalEdgeInH` is independent of the cut index. Its existing candidate lemmas are stronger than the recent cut-specific coherence wrappers:

1. `actualOriginalEdgeInH_injective`: exact fixed physical edge injection.
2. `actualOriginalEdgeInH_bottom_iff`: equality at the inherited bottom.
3. `actualOriginalEdgeInH_allPositiveCuts_iff`: preservation **and reflection** at *every* restored `ν.succ`, including universal top, for the SAME physical edge map.

The third lemma uses `actualOrderParentOldEdge_faithful` and `inheritedTrain_rel_succ`, so it does NOT need the cut-specific `ParentwiseRealization` or the additional strict-monotonicity carrier hypotheses. Hence do **not** put the recently added `actualOrderStageOriginalEdge_allProperCuts_iff` on the critical path. Retain it only as an independent alternate construction until the direct theorem receives exact-head verification, then consider deleting the redundant wrapper and its transitive checker imports.

## Genuine source-type reconciliation still required

The source *actual* edge type of the original relational target is
`{e : Set V // e ∈ supportCopies Asmall B}`, whereas the direct map takes
`(F c).OriginalEdge` where `F c : SummandPrivateTemplate V P X`.
`EdgeTrainLevels.actualSourceEdgeEquiv` supplies an equivalence from the dependent union of **induced** first-wagon support edges to the original source physical edges, provided the true original owner and first-wagon girth bound are used.

A final application must derive, for the specific selected EHN choice `c`, an equivalence
`φ_c : (F c).OriginalEdge ≃ {e : Set V // e ∈ supportCopies Asmall B}`
whose first projection satisfies
`(φ_c e)`'s original first-wagon owner = `e.1`.
It is NOT enough to prove merely that these two types have the same finite cardinality.

The following diagram must commute for each original physical edge:
```
original B physical A-edge -- φ_c.symm --> (F c).OriginalEdge
                                                 |
                                          selectedTaggedOriginalEdge
                                                 |
                                               G0 edge
                                                 |
                                        actualOriginalEdgeInH
                                                 |
                                             H physical edge
```

Then the source T relation transport must use the genuine *tail quotient*:
`Told.rel (ν.succ) a b ↔ Told.tailQuotient.rel ν [a]₁ [b]₁`.
The candidate `actualContractedChoiceTrain_rel_original_iff` already proves the component-side version, including universal top. The missing work is the exact definitional/equivalence identification of `F c`'s first-wagon labels with `Told.FirstWagon` and of the `T` parameter in `actualOriginalEdgeInH_allPositiveCuts_iff` with `Told.tailQuotient`, **not** another generic preservation-of-all-cuts lemma.

## Additional correctness boundary

The **large** edge type `Aold` used by the shortened Ramsey theorem and the **small** original coloured edge type `Asmall` used inside X are different. The candidate `actualOrderStage_canonicalTwoTypeTargetGirth` correctly retains both types and must be used for system girth. One-type canonical filling is not a justified shortcut.

Likewise, physical edge-train equality is not yet a full induced embedding of the ordered, coloured, partite relational T. The vertex map `τ_c`, actual induced edge equivalence `φ_c`, unary colours, ordering within each predicate and target strongness must be combined for the SAME selected pair `(i,c)`. The colour-word arrow must use that same pair.

## Recommended next exact proof obligations

1. Exhibit the actual selected `SummandPrivateTemplate` for each EHN choice, and prove its `oldCarrier` and `piece.localEdges` agree with the genuine induced first-wagon carriers/support of B. Construct `φ_c` via `actualSourceEdgeEquiv`.
2. Prove owner compatibility and original `Told.tailQuotient` compatibility for `φ_c`, including bottom and top.
3. Compose `φ_c` with the EXISTING fixed `actualOriginalEdgeInH` (rather than adding more cutwise wrappers).
4. Combine the existing two-edge-type target-girth candidate and the same selected pair's monochromatic arrow.
5. Perform exact-head Lean build, strict `#print axioms`, and full TeX compilation; only then promote validation marks.

**No proof completion or CI success is claimed here.**
