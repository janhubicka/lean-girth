import Girth.Forest

/-! # Transfer of join trees along identical pairwise intersections

In the circulation picture step, the intersections of two distinct full
standard copies are exactly those of their attached local gluing copies.
A vertex private to one larger standard copy creates a singleton occurrence
set; a vertex shared by two larger copies was already present in their local
gluing copies.  The same outer join tree therefore continues to satisfy the
running-intersection property.

This provides the direct bridge from a local forest of gluing copies to the
join-tree geometry of their full standard-picture extensions.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Enlarge the carriers of a family without changing any pairwise
intersection.  The join tree on the smaller carriers remains a join tree
on the enlarged carriers. -/
theorem JoinTree.transfer_of_pair_intersections
    {small large : ι → HypergraphPiece W}
    (J : JoinTree small)
    (hSub : ∀ i, (small i).carrier ⊆ (large i).carrier)
    (hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (large i).carrier ∩ (large j).carrier =
          (small i).carrier ∩ (small j).carrier) :
    JoinTree large where
  tree := J.tree
  isTree := J.isTree
  running := by
    classical
    intro x
    by_cases hOne :
        ({i : ι | x ∈ (large i).carrier}).Subsingleton
    · haveI : Subsingleton {i : ι | x ∈ (large i).carrier} :=
        ⟨by
          intro a b
          exact Subtype.ext (hOne a.property b.property)⟩
      exact SimpleGraph.Preconnected.of_subsingleton
    · rw [Set.not_subsingleton_iff] at hOne
      rcases hOne with ⟨a, ha, b, hb, hab⟩
      have hBoth :
          x ∈ (small a).carrier ∩ (small b).carrier := by
        rw [← hPair hab]
        exact ⟨ha, hb⟩
      have hOccurrence :
          {i : ι | x ∈ (large i).carrier} =
            {i : ι | x ∈ (small i).carrier} := by
        ext i
        constructor
        · intro hi
          by_cases hia : i = a
          · subst i
            exact hBoth.1
          · have hSmallPair :
                x ∈ (small i).carrier ∩ (small a).carrier := by
              rw [← hPair hia]
              exact ⟨hi, ha⟩
            exact hSmallPair.1
        · intro hi
          exact hSub i hi
      rw [hOccurrence]
      exact J.running x

/-- Pairwise allowed intersections survive a carrier enlargement when
every pairwise intersection stays unchanged and the old support edges
remain edges of the corresponding enlarged piece. -/
theorem pairwiseAllowed_transfer_of_pair_intersections
    {small large : ι → HypergraphPiece W}
    (hAllowed : PairwiseAllowed small)
    (hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (large i).carrier ∩ (large j).carrier =
          (small i).carrier ∩ (small j).carrier)
    (hEdges :
      ∀ i, (small i).edges ⊆ (large i).edges) :
    PairwiseAllowed large := by
  intro i j hij
  rcases hAllowed hij with hSmall | ⟨e, heI, heJ, hEq⟩
  · left
    rw [hPair hij]
    exact hSmall
  · right
    refine ⟨e, hEdges i heI, hEdges j heJ, ?_⟩
    rw [hPair hij]
    exact hEq

/-- A forest of local gluing pieces remains a forest after passing to
full standard-picture pieces with the same pairwise carrier intersections,
provided their common support edges are retained. -/
theorem ForestOfCopies.transfer_of_pair_intersections
    {small large : ι → HypergraphPiece W}
    (hForest : ForestOfCopies small)
    (hSub : ∀ i, (small i).carrier ⊆ (large i).carrier)
    (hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (large i).carrier ∩ (large j).carrier =
          (small i).carrier ∩ (small j).carrier)
    (hEdges : ∀ i, (small i).edges ⊆ (large i).edges) :
    ForestOfCopies large := by
  have hAllowed :
      PairwiseAllowed large :=
    pairwiseAllowed_transfer_of_pair_intersections
      hForest.pairwiseAllowed hPair hEdges
  refine ⟨hAllowed, ?_⟩
  rcases hForest.2 with hEmpty | hTree
  · exact Or.inl hEmpty
  · cases hTree with
    | intro J =>
        exact Or.inr ⟨J.transfer_of_pair_intersections hSub hPair⟩

end StructuralRamsey.Girth
