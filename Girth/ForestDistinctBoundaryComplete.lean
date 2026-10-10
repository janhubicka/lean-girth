import Girth.ForestDistinctBoundaryGirth
import Girth.ForestDistinctBoundaryAuxDelete

/-!
# All-distinct forest increment under exact physical boundary data

The all-distinct selected-piece family itself is a forest, not only
its pairwise intersections, once the finite exact geometric boundary
data are supplied. Local girth excludes every mandatory incidence
cycle; an extension tree carries all running intersections; pairwise
allowedness holds for all three node kinds; and the temporary physical
edge and formal-singleton members are erased by the verified one-edge
deletion theorem.

This is the FINITE DIRECT-INCREMENT EQUALITY-CASE interface. The
application still needs a separate theorem choosing its finite true
physical used-edge and represented-vertex labels from the selected
standard-picture family. It is not the recursive Ramsey arrow.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- A family of selected pieces with pairwise distinct containing
standard pictures forms a forest provided its actual boundary ports
are recorded by distinct physical edges and vertices and the local
hypergraph has the corresponding girth bound. -/
theorem selectedForest_of_distinctBoundary_localGirth
    [Fintype I] [Nonempty I] [Fintype E] [Fintype V]
    (selected : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (q : ℕ)
    (hEdgeInj : Function.Injective edge)
    (hVertexInj : Function.Injective vertex)
    (hUsedCard : Fintype.card E ≤ q)
    (hGirth : GirthGT K q)
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdge : ∀ e, edge e ∈ K)
    (hEdgeSub : ∀ e, edge e ⊆ S)
    (hVertexSub : ∀ v, vertex v ∈ S)
    (hPort : BoundaryPortExact selected S edge vertex port)
    (hAllCoreVerticesRepresented :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (E ⊕ V),
          x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier) →
        ∃ v : V, vertex v = x) :
    ForestOfCopies selected := by
  have hAcyclic :
      (boundaryPortSkeleton edge vertex port).IsAcyclic :=
    boundaryPortSkeleton_isAcyclic_of_localGirth
      edge vertex port K q hEdgeInj hVertexInj
      hUsedCard hEdge hGirth
  have hAugmented :
      ForestOfCopies
        (augmentedBoundaryPieces selected edge vertex) :=
    augmentedBoundary_forest_of_skeletonAcyclic
      selected S K edge vertex port hAcyclic hLinear
      hBoundary hCross hEdge hEdgeSub hVertexSub
      hPort hVertexInj hAllCoreVerticesRepresented
  exact selectedForest_of_augmentedBoundaryForest
    selected edge vertex hAugmented

end StructuralRamsey.Girth
