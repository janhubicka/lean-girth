import Girth.ForestLeafDeletion

/-!
# Helly's property for join-tree occurrence subtrees

A direct leaf-induction proof of the only Helly statement needed in
the small-trace argument: if every pair of vertices of a nonempty set
occurs together in some bag of a running-intersection family, then
one bag contains the whole set.

This avoids an external tree-Helly formalization.  Importantly the
leaf argument does NOT use pairwise-allowed intersections of pieces,
only the checked running-intersection property of JoinTree.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- If a nonempty set of vertices is pairwise covered by bags of a
finite join tree, one bag covers the set.  The condition also includes
the diagonal x=y, so singleton sets are covered without assuming a
separate vertex-cover hypothesis. -/
theorem JoinTree.pairCovered_in_one_bag
    {F : ι → HypergraphPiece W} [Fintype ι] [Nonempty ι]
    (J : JoinTree F)
    {K : Set W} (hK : K.Nonempty)
    (hPair :
      ∀ x : W, x ∈ K →
        ∀ y : W, y ∈ K →
          ∃ i : ι,
            x ∈ (F i).carrier ∧ y ∈ (F i).carrier) :
    ∃ i : ι, ∀ x : W, x ∈ K → x ∈ (F i).carrier := by
  classical
  by_cases hsub : Subsingleton ι
  · letI : Subsingleton ι := hsub
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    obtain ⟨x₀, hx₀⟩ := hK
    refine ⟨i₀, ?_⟩
    intro x hx
    obtain ⟨i, hxi, _⟩ := hPair x hx x₀ hx₀
    have hi : i = i₀ := Subsingleton.elim i i₀
    simpa only [hi] using hxi
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _⟩ :=
      J.exists_leaf_attachment
    by_cases hLeaf : ∀ x : W, x ∈ K → x ∈ (F leaf).carrier
    · exact ⟨leaf, hLeaf⟩
    · push_neg at hLeaf
      obtain ⟨x₀, hx₀, hx₀NotLeaf⟩ := hLeaf
      let reindexRest :
          {j : ι // j ≠ leaf} ≃
            {j : ι // j ∈ (({leaf} : Set ι)ᶜ)} :=
        Equiv.subtypeEquivRight (fun j => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
      let JRest :
          JoinTree (fun j : {t : ι // t ≠ leaf} => F j.1) := by
        simpa [erasePiece, reindexRest] using
          (J.eraseLeaf hadj huniq).reindex reindexRest
      have hPairRest :
          ∀ x : W, x ∈ K →
            ∀ y : W, y ∈ K →
              ∃ j : {t : ι // t ≠ leaf},
                x ∈ (F j.1).carrier ∧
                y ∈ (F j.1).carrier := by
        intro x hx y hy
        obtain ⟨i, hxi, hyi⟩ := hPair x hx y hy
        by_cases hi : i = leaf
        · subst i
          obtain ⟨j, hx₀j, hxj⟩ := hPair x₀ hx₀ x hx
          obtain ⟨k, hx₀k, hyk⟩ := hPair x₀ hx₀ y hy
          have hjNe : j ≠ leaf := by
            intro hj
            subst j
            exact hx₀NotLeaf hx₀j
          have hkNe : k ≠ leaf := by
            intro hk
            subst k
            exact hx₀NotLeaf hx₀k
          have hxParent :
              x ∈ (F parent).carrier :=
            J.mem_parent_of_mem_leaf_and_other
              hadj huniq hjNe hxi hxj
          have hyParent :
              y ∈ (F parent).carrier :=
            J.mem_parent_of_mem_leaf_and_other
              hadj huniq hkNe hyi hyk
          exact ⟨⟨parent, hadj.ne.symm⟩, hxParent, hyParent⟩
        · exact ⟨⟨i, hi⟩, hxi, hyi⟩
      letI : Nonempty {j : ι // j ≠ leaf} :=
        ⟨⟨parent, hadj.ne.symm⟩⟩
      have hcard :
          Fintype.card {j : ι // j ≠ leaf} < Fintype.card ι := by
        apply Fintype.card_lt_of_injective_not_surjective
          (fun j : {t : ι // t ≠ leaf} => j.1)
          Subtype.val_injective
        intro hsurj
        obtain ⟨j, hj⟩ := hsurj leaf
        exact j.2 hj
      obtain ⟨j, hj⟩ :=
        JoinTree.pairCovered_in_one_bag JRest hK hPairRest
      exact ⟨j.1, hj⟩
termination_by Fintype.card ι
decreasing_by
  exact hcard

end StructuralRamsey.Girth
