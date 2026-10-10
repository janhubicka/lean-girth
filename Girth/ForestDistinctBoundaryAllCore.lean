import Girth.ForestDistinctBoundaryComplete

/-!
# An entire finite core is a canonical vertex-node family

The all-distinct incidence argument does not need to choose a
separate list of "used singleton vertices" or "vertices belonging
to used whole-edge boundaries". Use ALL vertices of the finite local
core as formal singleton incidence nodes, including isolated ones.
Every original/auxiliary occurrence at a core vertex then has a
canonical anchor by construction. This discharges injectivity,
core-membership and represented-occurrence hypotheses simultaneously.

Only the used DISTINCT physical whole-edge labels and each selected
member's exact boundary port remain to be chosen.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E : Type v}

/-- A finite core itself is a canonical choice of the auxiliary
vertex-index type; core-vertex completeness becomes automatic. -/
theorem selectedForest_of_distinctBoundary_allCoreVertices
    [Fintype I] [Nonempty I] [Fintype E]
    (selected : I → HypergraphPiece W)
    (S : Set W) [Fintype S]
    (K : Set (Set W))
    (edge : E → Set W)
    (port : I → Option (E ⊕ S))
    (q : ℕ)
    (hEdgeInj : Function.Injective edge)
    (hUsedCard : Fintype.card E ≤ q)
    (hGirth : GirthGT K q)
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdge : ∀ e, edge e ∈ K)
    (hEdgeSub : ∀ e, edge e ⊆ S)
    (hPort : BoundaryPortExact selected S edge
      (fun v : S => (v : W)) port) :
    ForestOfCopies selected := by
  have hVertexSub : ∀ v : S, (v : W) ∈ S := by
    intro v
    exact v.2
  have hAllCore :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (E ⊕ S),
          x ∈ (augmentedBoundaryPieces
            selected edge (fun v : S => (v : W)) z).carrier) →
        ∃ v : S, (v : W) = x := by
    intro x hx _
    exact ⟨⟨x, hx⟩, rfl⟩
  exact selectedForest_of_distinctBoundary_localGirth
    selected S K edge (fun v : S => (v : W)) port q
    hEdgeInj Subtype.val_injective hUsedCard hGirth
    hLinear hBoundary hCross hEdge hEdgeSub
    hVertexSub hPort hAllCore

end StructuralRamsey.Girth
