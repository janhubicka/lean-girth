import Girth.ForestDistinctBoundaryComplete

/-!
# Finite one-edge families in a high-girth hypergraph

A specialization of the already verified distinct-boundary incidence
construction: use every genuine support edge as both a selected piece and
an actual boundary edge. A temporary node for each ambient vertex
supplies the running-intersection anchor. All of these temporary nodes
are erased by the verified all-distinct boundary theorem.

This supplies the missing support-edge base for the strengthened
covered-family pure-to-mixed reduction, even if the owner copy has
isolated vertices. It assumes a finite ambient vertex type, as in the
circulation manuscript.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- At most m DISTINCT support edges of a finite hypergraph with Berge
girth greater than m form a forest of one-edge members.

This does not require that any chosen vertex be incident with an edge.
If there are no selected support edges the forest condition is vacuous;
the nonempty version is the one needed to initialize the local join
tree after ownership of selected edge pieces. -/
theorem forest_oneEdge_family_of_girthGT
    [Fintype W] [Fintype I] [Nonempty I]
    (edge : I → Set W)
    (hEdgeInj : Function.Injective edge)
    (m : ℕ)
    (hm : 2 ≤ m)
    (hCard : Fintype.card I ≤ m)
    (hGirth : GirthGT (Set.range edge) m) :
    ForestOfCopies
      (fun i : I => HypergraphPiece.oneEdge (edge i)) := by
  classical
  let selected : I → HypergraphPiece W :=
    fun i => HypergraphPiece.oneEdge (edge i)
  let K : Set (Set W) := Set.range edge
  let S : Set W := Set.univ
  let vertex : W → W := id
  let port : I → Option (I ⊕ W) :=
    fun i => some (.inl i)
  have hLinear : LinearEdgeSet K := by
    intro e f he hf hne
    exact pairwise_subsingleton_of_girthGT_two
      (girthGT_mono hGirth hm) he hf hne
  have hBoundary :
      ∀ i, SmallOrWholeEdgeBoundary K S (selected i) := by
    intro i
    right
    refine ⟨edge i, ⟨i, rfl⟩, ?_, ?_⟩
    · simp [selected, HypergraphPiece.oneEdge]
    · simp [selected, HypergraphPiece.oneEdge, S]
  have hCross :
      ∀ ⦃i j : I⦄, i ≠ j →
        (selected i).carrier ∩ (selected j).carrier ⊆ S := by
    intro i j _
    exact Set.subset_univ _
  have hEdge : ∀ i : I, edge i ∈ K := by
    intro i
    exact ⟨i, rfl⟩
  have hEdgeSub : ∀ i : I, edge i ⊆ S := by
    intro i
    exact Set.subset_univ _
  have hVertexSub : ∀ v : W, vertex v ∈ S := by
    intro v
    simp [vertex, S]
  have hPort : BoundaryPortExact selected S edge vertex port := by
    intro i
    simp [BoundaryPortExact, selected, S, port,
      HypergraphPiece.oneEdge]
  have hRepresented :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (I ⊕ W),
          x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier) →
        ∃ v : W, vertex v = x := by
    intro x _ _
    exact ⟨x, rfl⟩
  have hResult :=
    selectedForest_of_distinctBoundary_localGirth
      selected S K edge vertex port m
      hEdgeInj (fun _ _ h => h) hCard hGirth
      hLinear hBoundary hCross hEdge hEdgeSub
      hVertexSub hPort hRepresented
  exact hResult

end StructuralRamsey.Girth
