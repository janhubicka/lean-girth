import Girth.ForestDistinctBoundaryRunningAll
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The finite mandatory skeleton of the all-distinct boundary forest

We form exactly the edges that a join tree must retain:

* each selected copy has at most one link, to its whole boundary
  edge node or singleton boundary vertex node;
* each real boundary edge node is linked to exactly the physical
  vertex nodes that lie in it.

All other edges are absent. An acyclic skeleton can always be
extended to a spanning tree, since the complete graph is connected.
Every such extension preserves the mandatory links; the checked
running-intersection and pairwise-allowed kernels then make it a
join tree of the augmented family.

The genuinely remaining task is the finite acyclicity theorem for
this skeleton, derived from local girth >q on at most q DISTINCT
physical boundary edges. The selected leaves cannot create cycles,
but that final implication is not asserted here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- Exact mandatory graph: selected members have at most one port,
and physical edge--vertex links are the ordinary incidence relation.
In particular, no two selected labels are adjacent and no two
boundary-vertex nodes are adjacent. -/
def boundaryPortSkeleton
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V)) :
    SimpleGraph (I ⊕ (E ⊕ V)) where
  Adj a b :=
    match a, b with
    | .inl i, .inr z => port i = some z
    | .inr z, .inl i => port i = some z
    | .inr (.inl e), .inr (.inr v) => vertex v ∈ edge e
    | .inr (.inr v), .inr (.inl e) => vertex v ∈ edge e
    | _, _ => False
  symm := ⟨by
    intro a b h
    cases a with
    | inl i =>
      cases b with
      | inl j => exact False.elim h
      | inr z => exact h
    | inr z =>
      cases b with
      | inl i => exact h
      | inr t =>
        cases z with
        | inl e =>
          cases t with
          | inl f => exact False.elim h
          | inr v => exact h
        | inr v =>
          cases t with
          | inl e => exact h
          | inr u => exact False.elim h⟩
  loopless := ⟨by
    intro a
    cases a with
    | inl i => simp
    | inr t =>
      cases t <;> simp⟩

@[simp] theorem boundaryPortSkeleton_adj_selected
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (i : I) (z : E ⊕ V) :
    (boundaryPortSkeleton edge vertex port).Adj
      (.inl i) (.inr z) ↔ port i = some z :=
  Iff.rfl

@[simp] theorem boundaryPortSkeleton_adj_incidence
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (e : E) (v : V) :
    (boundaryPortSkeleton edge vertex port).Adj
      (.inr (.inl e)) (.inr (.inr v)) ↔
      vertex v ∈ edge e :=
  Iff.rfl

/-- Every acyclic mandatory skeleton can be extended to a tree
retaining ALL of its selected-port and physical incidence edges.
Only nonemptiness of selected labels is needed; finiteness is not. -/
theorem exists_tree_over_boundaryPortSkeleton
    [Nonempty I]
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (hAcyclic : (boundaryPortSkeleton edge vertex port).IsAcyclic) :
    ∃ T : SimpleGraph (I ⊕ (E ⊕ V)),
      boundaryPortSkeleton edge vertex port ≤ T ∧
      T.IsTree := by
  classical
  letI : Nonempty (I ⊕ (E ⊕ V)) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  obtain ⟨T, hContains, _hTop, hTree⟩ :=
    (SimpleGraph.connected_top : (⊤ : SimpleGraph (I ⊕ (E ⊕ V))).Connected)
      .exists_isTree_le_of_le_of_isAcyclic le_top hAcyclic
  exact ⟨T, hContains, hTree⟩

/-- The full augmented boundary family is a forest once its
mandatory incidence skeleton is acyclic, assuming the EXACT
distinct-owner source geometry and physical vertex representation.
This removes the external join-tree existence premise from the
running-intersection theorem, leaving only skeleton acyclicity. -/
theorem augmentedBoundary_forest_of_skeletonAcyclic
    [Nonempty I]
    (selected : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (edge : E → Set W) (vertex : V → W)
    (port : I → Option (E ⊕ V))
    (hAcyclic : (boundaryPortSkeleton edge vertex port).IsAcyclic)
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (selected i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
      (selected i).carrier ∩ (selected j).carrier ⊆ S)
    (hEdge : ∀ e : E, edge e ∈ K)
    (hEdgeSub : ∀ e : E, edge e ⊆ S)
    (hVertexSub : ∀ v : V, vertex v ∈ S)
    (hPort : BoundaryPortExact selected S edge vertex port)
    (hVertexInj : Function.Injective vertex)
    (hAllCoreVerticesRepresented :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (E ⊕ V),
          x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier) →
        ∃ v : V, vertex v = x) :
    ForestOfCopies
      (augmentedBoundaryPieces selected edge vertex) := by
  obtain ⟨T, hSkeleton, hTree⟩ :=
    exists_tree_over_boundaryPortSkeleton edge vertex port hAcyclic
  have hAttach : ∀ i : I, ∀ z : E ⊕ V,
      port i = some z → T.Adj (.inl i) (.inr z) := by
    intro i z hp
    apply hSkeleton
    exact hp
  have hIncidence : ∀ e : E, ∀ v : V,
      vertex v ∈ edge e →
      T.Adj (.inr (.inl e)) (.inr (.inr v)) := by
    intro e v he
    apply hSkeleton
    exact he
  exact augmentedBoundary_forest_of_incidenceTree
    selected S K edge vertex port T hTree hLinear
    hBoundary hCross hEdge hEdgeSub hVertexSub
    hPort hAttach hIncidence hVertexInj
    hAllCoreVerticesRepresented

end StructuralRamsey.Girth
