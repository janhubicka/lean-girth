import Girth.ForestGirth
import Girth.ForestTreeRewire

/-! # Star forests

The initial picture base case repeatedly uses the same elementary forest:
one ambient B-support piece is the centre and selected A-support edges are
leaves.  This file packages that construction independently of the partite
machinery.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- One centre piece together with one-edge leaves. -/
def centerWithEdgeLeaves
    (F : HypergraphPiece W) (e : ι → Set W) :
    Option ι → HypergraphPiece W
  | none => F
  | some i => oneEdgePiece (e i)

/-- A centre piece with pairwise-linearly-intersecting edge leaves is a forest.
The join tree is the literal star centred at the ambient piece. -/
theorem forest_centerWithEdgeLeaves
    (F : HypergraphPiece W)
    (e : ι → Set W)
    (hEdge : ∀ i, e i ∈ F.edges)
    (hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (e i ∩ e j).Subsingleton) :
    ForestOfCopies (centerWithEdgeLeaves F e) := by
  classical
  have hAllowed : PairwiseAllowed (centerWithEdgeLeaves F e) := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some j =>
            right
            refine ⟨e j, hEdge j, ?_, ?_⟩
            · simp [centerWithEdgeLeaves, oneEdgePiece]
            · exact Set.inter_eq_right.mpr (F.edge_subset (hEdge j))
    | some i =>
        cases b with
        | none =>
            right
            refine ⟨e i, ?_, hEdge i, ?_⟩
            · simp [centerWithEdgeLeaves, oneEdgePiece]
            · exact Set.inter_eq_left.mpr (F.edge_subset (hEdge i))
        | some j =>
            left
            have hij : i ≠ j := by
              intro h
              apply hab
              simpa [h]
            simpa [centerWithEdgeLeaves, oneEdgePiece] using hPair hij
  refine ⟨hAllowed, Or.inr ⟨?_⟩⟩
  refine
    { tree := SimpleGraph.starGraph (none : Option ι)
      isTree := SimpleGraph.isTree_starGraph (none : Option ι)
      running := ?_ }
  intro x
  by_cases hx : x ∈ F.carrier
  · have hcenter :
        (none : Option ι) ∈
          {k : Option ι |
            x ∈ (centerWithEdgeLeaves F e k).carrier} := by
      exact hx
    exact
      starGraph_induce_preconnected_of_mem_center
        (none : Option ι) hcenter
  · intro a b
    have hFalse : False := by
      cases h : a.1 with
      | none =>
          have ha : x ∈ F.carrier := by
            simpa [h, centerWithEdgeLeaves] using a.2
          exact hx ha
      | some i =>
          have ha : x ∈ e i := by
            simpa [h, centerWithEdgeLeaves, oneEdgePiece] using a.2
          exact hx (F.edge_subset (hEdge i) ha)
    exact hFalse.elim

end StructuralRamsey.Girth
