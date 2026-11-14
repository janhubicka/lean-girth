import Girth.ForestSeparatorCrossAllowed
import Girth.ForestJoinGlue

/-!
# Binary gluing for small or common-edge separators

This is the recursive leaf step underlying the manuscript's *general*
join-tree lifting lemma. In particular an isolated singleton separator
does not have to belong to any local forest member. An empty/one-point
cross carrier allows the two join trees to be joined at arbitrary or
suitable nodes. A common-edge separator requires its one-edge member
on each side, kept until after gluing.

Unlike the older outer-tree lifting theorem, this binary argument
places NO edge-covering request on a singleton separator.

Both statements are source-level Lean candidates awaiting compilation
and an exact-head axiom audit.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I J : Type v}

/-- Two nonempty finite forests can be joined whenever all their
cross-family shared vertices form at most one point.

The connecting nodes are chosen to contain the shared vertex if
there is one; otherwise any two nodes work. No singleton helper
or edge request is needed. -/
theorem forestOfCopies_sum_of_subsingleton_overlap
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (hG : ForestOfCopies G)
    (hSmall :
      ((⋃ i : I, (F i).carrier) ∩
        (⋃ j : J, (G j).carrier)).Subsingleton) :
    ForestOfCopies (sumPieces F G) := by
  classical
  let S : Set W :=
    (⋃ i : I, (F i).carrier) ∩
      (⋃ j : J, (G j).carrier)
  have hS : S.Subsingleton := hSmall
  have hCrossAllowed :
      ∀ i : I, ∀ j : J, AllowedIntersection (F i) (G j) := by
    intro i j
    left
    intro x hx y hy
    apply hS
    · exact ⟨Set.mem_iUnion.mpr ⟨i, hx.1⟩,
        Set.mem_iUnion.mpr ⟨j, hx.2⟩⟩
    · exact ⟨Set.mem_iUnion.mpr ⟨i, hy.1⟩,
        Set.mem_iUnion.mpr ⟨j, hy.2⟩⟩
  obtain ⟨JF⟩ := hF.joinTree_of_nonempty
  obtain ⟨JG⟩ := hG.joinTree_of_nonempty
  by_cases hSome : S.Nonempty
  · obtain ⟨x, hxS⟩ := hSome
    obtain ⟨i0, hxi⟩ := Set.mem_iUnion.mp hxS.1
    obtain ⟨j0, hxj⟩ := Set.mem_iUnion.mp hxS.2
    have hCrossOcc :
        ∀ (y : W) (i : I) (j : J),
          y ∈ (F i).carrier →
          y ∈ (G j).carrier →
          y ∈ (F i0).carrier ∧ y ∈ (G j0).carrier := by
      intro y i j hyi hyj
      have hyS : y ∈ S :=
        ⟨Set.mem_iUnion.mpr ⟨i, hyi⟩,
          Set.mem_iUnion.mpr ⟨j, hyj⟩⟩
      have hyx : y = x := hS hyS hxS
      subst y
      exact ⟨hxi, hxj⟩
    exact forestOfCopies_sumBridge
      JF JG hF.pairwiseAllowed hG.pairwiseAllowed
      i0 j0 hCrossOcc hCrossAllowed
  · let i0 : I := Classical.choice (inferInstance : Nonempty I)
    let j0 : J := Classical.choice (inferInstance : Nonempty J)
    have hCrossOcc :
        ∀ (y : W) (i : I) (j : J),
          y ∈ (F i).carrier →
          y ∈ (G j).carrier →
          y ∈ (F i0).carrier ∧ y ∈ (G j0).carrier := by
      intro y i j hyi hyj
      have hyS : y ∈ S :=
        ⟨Set.mem_iUnion.mpr ⟨i, hyi⟩,
          Set.mem_iUnion.mpr ⟨j, hyj⟩⟩
      exact (hSome ⟨y, hyS⟩).elim
    exact forestOfCopies_sumBridge
      JF JG hF.pairwiseAllowed hG.pairwiseAllowed
      i0 j0 hCrossOcc hCrossAllowed

/-- Binary gluing across a complete common edge: the two local
forests each retain a member equal to the one-edge piece e+. The
only geometric requirement is that every cross-member
intersection lies in e.

In particular the same e+ may be represented by two DISTINCT
labels. Both labels remain during this gluing step; a later
short-auxiliary deletion may discard either duplicate. -/
theorem forestOfCopies_sum_of_common_edge
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (hG : ForestOfCopies G)
    (e : Set W)
    (i0 : I) (j0 : J)
    (hRequestF : F i0 = HypergraphPiece.oneEdge e)
    (hRequestG : G j0 = HypergraphPiece.oneEdge e)
    (hCross :
      ∀ i : I, ∀ j : J,
        (F i).carrier ∩ (G j).carrier ⊆ e) :
    ForestOfCopies (sumPieces F G) := by
  classical
  obtain ⟨JF⟩ := hF.joinTree_of_nonempty
  obtain ⟨JG⟩ := hG.joinTree_of_nonempty
  have hCrossAllowed :
      ∀ i : I, ∀ j : J, AllowedIntersection (F i) (G j) := by
    intro i j
    apply allowedIntersection_cross_of_common_request
      (F i) (G j) e (hCross i j)
    · exact allowedIntersection_with_local_request
        hF.pairwiseAllowed i0 e hRequestF i
    · exact allowedIntersection_with_local_request
        hG.pairwiseAllowed j0 e hRequestG j
  have hCrossOcc :
      ∀ (x : W) (i : I) (j : J),
        x ∈ (F i).carrier →
        x ∈ (G j).carrier →
        x ∈ (F i0).carrier ∧ x ∈ (G j0).carrier := by
    intro x i j hxi hxj
    have hxEdge : x ∈ e := hCross i j ⟨hxi, hxj⟩
    rw [hRequestF, hRequestG]
    exact ⟨hxEdge, hxEdge⟩
  exact forestOfCopies_sumBridge
    JF JG hF.pairwiseAllowed hG.pairwiseAllowed
    i0 j0 hCrossOcc hCrossAllowed

/-- Binary gluing with a separator which is either subsingleton
or carried by a retained one-edge request on BOTH sides. This is
the precise leaf-induction interface of the general join-tree
lifting argument, including the case where an isolated singleton
is not present in any local member. -/
theorem forestOfCopies_sum_of_smallOrEdge_overlap
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {F : I → HypergraphPiece W}
    {G : J → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (hG : ForestOfCopies G)
    (hSeparator :
      ((⋃ i : I, (F i).carrier) ∩
        (⋃ j : J, (G j).carrier)).Subsingleton ∨
      ∃ (e : Set W) (i0 : I) (j0 : J),
        F i0 = HypergraphPiece.oneEdge e ∧
        G j0 = HypergraphPiece.oneEdge e ∧
        ((⋃ i : I, (F i).carrier) ∩
          (⋃ j : J, (G j).carrier)) ⊆ e) :
    ForestOfCopies (sumPieces F G) := by
  rcases hSeparator with hSmall | ⟨e, i0, j0, hReqF, hReqG, hSub⟩
  · exact forestOfCopies_sum_of_subsingleton_overlap hF hG hSmall
  · apply forestOfCopies_sum_of_common_edge
      hF hG e i0 j0 hReqF hReqG
    intro i j x hx
    apply hSub
    exact ⟨Set.mem_iUnion.mpr ⟨i, hx.1⟩,
      Set.mem_iUnion.mpr ⟨j, hx.2⟩⟩

end StructuralRamsey.Girth
