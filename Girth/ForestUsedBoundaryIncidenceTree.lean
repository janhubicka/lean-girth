import Girth.BoundaryIncidenceCompletion
import Girth.Berge

/-!
# The used physical boundary edges admit an incidence-tree completion

In the all-distinct branch of the direct forest increment, the
number of DISTINCT whole-edge boundaries is at most the size q of
the selected family. They are real edges of the local hypergraph K.

Local girth greater than q makes the incidence graph of these
distinct used physical edges acyclic. Its finite active-vertex
subgraph can be connected to a tree by adding only edges between
EDGE-NODES: no new adjacency to a real boundary vertex is created.

This is the graph-theoretic core needed to attach selected members
and formal singleton boundary nodes. It is not yet a join tree of
the full augmented selected-piece family; those attachments are the
remaining separate interface.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- All distinct used whole-support boundary edges can be arranged
in an incidence tree retaining every physical edge--vertex incidence,
using the local girth bound at exactly the finite used-edge budget. -/
theorem exists_usedBoundaryIncidenceTree_of_localGirth
    [Fintype E] [Nonempty E]
    (edge : E → Set W)
    (hEdgeInj : Function.Injective edge)
    (K : Set (Set W))
    (hEdge : ∀ e : E, edge e ∈ K)
    (q : ℕ)
    (hCard : Fintype.card E ≤ q)
    (hGirth : GirthGT K q) :
    ∃ T : SimpleGraph (E ⊕ BoundaryActiveVertex edge),
      boundaryIncidenceGraph (activeBoundaryEdge edge) ≤ T ∧
      T ≤ boundaryIncidenceCompletionGraph edge ∧
      T.IsTree := by
  have hSubset : Set.range edge ⊆ K := by
    rintro _ ⟨e, rfl⟩
    exact hEdge e
  have hSmallGirth : GirthGT (Set.range edge) q :=
    girthGT_of_subset hSubset hGirth
  have hAcyclic : (boundaryIncidenceGraph edge).IsAcyclic :=
    boundaryIncidenceGraph_isAcyclic_of_girthGT
      edge hEdgeInj q hCard hSmallGirth
  exact exists_boundaryIncidenceCompletionTree edge hAcyclic

end StructuralRamsey.Girth
