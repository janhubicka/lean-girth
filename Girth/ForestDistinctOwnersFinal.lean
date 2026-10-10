import Girth.ForestDistinctBoundaryCanonical

/-!
# Fully quantified all-distinct direct forest increment

This closes the ABSTRACT EQUALITY CASE of the direct forest increment:
q selected pieces in pairwise different full-standard owners, with
carrier overlaps confined to the finite local core and the exact
small-or-whole-edge boundary hypothesis, form a forest as soon as the
local edge system is linear and has girth above q. No external
physical edge-label, vertex-label, port, incidence-tree, or deletion
premise remains.

The theorem does NOT establish that a particular picture-step family
satisfies these geometric hypotheses; applying it to the manuscript
is a separate interface. It also does NOT prove the local Ramsey
witness or the smaller-containing-piece branch.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- The all-distinct selected family is a forest from the geometric
boundary hypothesis and local girth alone. -/
theorem selectedForest_of_distinctOwners_localGirth
    [Fintype I] [Nonempty I]
    (selected : I → HypergraphPiece W)
    (S : Set W) [Fintype S]
    (K : Set (Set W)) (q : ℕ)
    (hSelectedCard : Fintype.card I ≤ q)
    (hGirth : GirthGT K q)
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S) :
    ForestOfCopies selected := by
  classical
  let E := UsedWholeBoundaryEdge selected S
  let edge : E → Set W := fun e => (e : Set W)
  obtain ⟨port, hPort⟩ :=
    exists_canonicalBoundaryPorts selected S
  have hEdgeInj : Function.Injective edge := Subtype.val_injective
  have hCard : Fintype.card E ≤ q :=
    (usedWholeBoundary_card_le selected S).trans hSelectedCard
  have hEdge : ∀ e : E, edge e ∈ K := by
    intro e
    exact usedWholeBoundary_mem_local selected S K hBoundary e
  have hEdgeSub : ∀ e : E, edge e ⊆ S := by
    intro e
    exact usedWholeBoundary_subset_core selected S e
  exact selectedForest_of_distinctBoundary_allCoreVertices
    selected S K edge port q hEdgeInj hCard hGirth
    hLinear hBoundary hCross hEdge hEdgeSub hPort

end StructuralRamsey.Girth
