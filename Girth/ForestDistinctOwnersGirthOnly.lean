import Girth.ForestDistinctOwnersFinal

/-!
# Girth-only equality case of the direct forest increment

No independent local linearity assumption is needed in the
all-distinct case. Ordinary local Berge girth greater than q, with
q ≥ 2, already forces every pair of distinct local support edges
to have a subsingleton intersection.

This is the natural statement to quote in circulation Lemma
`forestincrement`, conditional on exact distinct-owner boundary
geometry. It does not supply the missing local Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- For pairwise distinct full-standard owners, core girth and
the exact small-or-own-whole-edge boundary condition alone imply
that the selected mixed A/B family is a forest. -/
theorem selectedForest_of_distinctOwners_girthOnly
    [Fintype I] [Nonempty I]
    (selected : I → HypergraphPiece W)
    (S : Set W) [Fintype S]
    (K : Set (Set W)) (q : ℕ)
    (hq : 2 ≤ q)
    (hSelectedCard : Fintype.card I ≤ q)
    (hGirth : GirthGT K q)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S) :
    ForestOfCopies selected := by
  have hLinear : LinearEdgeSet K := by
    intro e f he hf hne
    exact pairwise_subsingleton_of_girthGT_two
      (girthGT_mono hGirth hq) he hf hne
  exact selectedForest_of_distinctOwners_localGirth
    selected S K q hSelectedCard hGirth
    hLinear hBoundary hCross

end StructuralRamsey.Girth
