import Girth.ForestCompletionGlobalBridge
import Girth.ForestSingleEdge

/-! # One-edge requests at separators of an outer forest

The old forest-completion invariant is applied independently at each selected
standard copy. Besides the tested members assigned to that copy, its request
contains one A-support edge for every neighbour in the outer join tree.

A separator is empty, a singleton, or a common support edge. If all vertices
of the outer pieces lie on support edges, a support edge in the first piece
covers every such separator. Ambient girth greater than two guarantees that
this choice is *exactly* the common edge whenever the separator is not
subsingleton. No separate exact-separator hypothesis is necessary.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

namespace HypergraphPiece

/-- The one-edge hypergraph piece on a prescribed support edge. -/
def oneEdge (e : Set W) : HypergraphPiece W where
  carrier := e
  edges := {e}
  edge_subset_carrier := by
    intro f hf
    have hEq : f = e := by simpa using hf
    subst f
    exact Set.Subset.rfl

@[simp]
theorem oneEdge_carrier (e : Set W) :
    (oneEdge e).carrier = e := rfl

@[simp]
theorem oneEdge_isOneEdge (e : Set W) :
    (oneEdge e).IsOneEdge := rfl

end HypergraphPiece

/-- Every separator between two distinct outer members is contained in
one support edge of the first member. Only nonempty support-edge families and
vertex coverage by support edges are needed. -/
theorem exists_support_edge_covering_separator
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (hNonempty : ∀ q : Q, (P q).edges.Nonempty)
    (hCover :
      ∀ q (x : W), x ∈ (P q).carrier →
        ∃ e : Set W, e ∈ (P q).edges ∧ x ∈ e)
    {q r : Q} (hqr : q ≠ r) :
    ∃ e : Set W, e ∈ (P q).edges ∧
      (P q).carrier ∩ (P r).carrier ⊆ e := by
  classical
  rcases hOuter hqr with hSmall | ⟨e, heq, _her, hInter⟩
  · by_cases hSome : ((P q).carrier ∩ (P r).carrier).Nonempty
    · rcases hSome with ⟨x, hx⟩
      obtain ⟨e, he, hxe⟩ := hCover q x hx.1
      refine ⟨e, he, ?_⟩
      intro y hy
      have hyx : y = x := hSmall hy hx
      exact hyx ▸ hxe
    · obtain ⟨e, he⟩ := hNonempty q
      refine ⟨e, he, ?_⟩
      intro x hx
      exact (hSome ⟨x, hx⟩).elim
  · refine ⟨e, heq, ?_⟩
    rw [hInter]

/-- If the ambient support is linear, any chosen support edge covering a
non-subsingleton separator is necessarily that separator itself. -/
theorem separator_edge_exact_of_ambient_girth
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    {q r : Q} (hqr : q ≠ r)
    {e : Set W}
    (he : e ∈ (P q).edges)
    (hCover : (P q).carrier ∩ (P r).carrier ⊆ e)
    (hBig : ¬((P q).carrier ∩ (P r).carrier).Subsingleton) :
    e = (P q).carrier ∩ (P r).carrier := by
  rcases hOuter hqr with hSmall | ⟨e₀, he₀, _heR, hInter⟩
  · exact (hBig hSmall).elim
  · by_cases hEq : e₀ = e
    · exact hEq.symm.trans hInter.symm
    · have hLinear :
          (e₀ ∩ e).Subsingleton :=
        pairwise_subsingleton_of_girthGT_two hGirth
          (hEdges q he₀) (hEdges q he) hEq
      have hSubset : e₀ ⊆ e := by
        intro x hx
        apply hCover
        rw [hInter]
        exact hx
      have hSmall₀ : e₀.Subsingleton := by
        intro x hx y hy
        exact hLinear ⟨hx, hSubset hx⟩ ⟨hy, hSubset hy⟩
      apply (hBig ?_).elim
      rw [hInter]
      exact hSmall₀

/-- Construct compatible one-edge connector pieces for every oriented edge
of a join tree. Their carriers cover the outer separator and coincide with
it whenever the separator is a whole support edge. -/
theorem exists_oneEdge_separator_requests
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (J : JoinTree P)
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    (hNonempty : ∀ q, (P q).edges.Nonempty)
    (hCover :
      ∀ q (x : W), x ∈ (P q).carrier →
        ∃ e : Set W, e ∈ (P q).edges ∧ x ∈ e) :
    ∃ separator :
        (q : Q) → J.tree.neighborSet q → HypergraphPiece W,
      ∀ q r,
        (separator q r).IsOneEdge ∧
        (separator q r).carrier ⊆ (P q).carrier ∧
        (P q).carrier ∩ (P r.1).carrier ⊆
          (separator q r).carrier ∧
        (¬((P q).carrier ∩ (P r.1).carrier).Subsingleton →
          (separator q r).carrier =
            (P q).carrier ∩ (P r.1).carrier) := by
  classical
  have hChoice (q : Q) (r : J.tree.neighborSet q) :
      ∃ e : Set W, e ∈ (P q).edges ∧
        (P q).carrier ∩ (P r.1).carrier ⊆ e :=
    exists_support_edge_covering_separator
      hOuter hNonempty hCover r.2.ne
  let edge (q : Q) (r : J.tree.neighborSet q) : Set W :=
    Classical.choose (hChoice q r)
  let separator (q : Q) (r : J.tree.neighborSet q) :
      HypergraphPiece W := HypergraphPiece.oneEdge (edge q r)
  refine ⟨separator, ?_⟩
  intro q r
  have hs := Classical.choose_spec (hChoice q r)
  dsimp [separator]
  refine ⟨HypergraphPiece.oneEdge_isOneEdge _, ?_, ?_, ?_⟩
  · exact (P q).edge_subset hs.1
  · exact hs.2
  · intro hBig
    exact separator_edge_exact_of_ambient_girth
      hOuter hEdges hGirth r.2.ne hs.1 hs.2 hBig

end StructuralRamsey.Girth
