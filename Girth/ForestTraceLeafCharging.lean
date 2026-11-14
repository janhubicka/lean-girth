import Girth.ForestLeafDeletion

/-!
# Private vertices and distinct representatives in join trees

A concrete combinatorial component of the small-trace argument.  It is
independent of chordality and uses only the pre-existing finite join-tree
leaf and leaf-deletion API.

An antichain of nonempty bags admitting a join tree has a system of
distinct representatives.  In the trace proof, this provides the sharp
bound on the number of maximal traces once a join tree on those traces
has been obtained.  Constructing that join tree from the manuscript's
*local* extension hypothesis remains a separate obligation.

This module must not be marked as Lean-verified without an exact-head
kernel build and #print axioms.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- A leaf of a nontrivial join tree of pairwise incomparable carriers
contains a vertex absent from every other carrier.  This is the exact
private-vertex argument used in the trace-counting induction. -/
theorem JoinTree.exists_leaf_private_vertex
    {F : ι → HypergraphPiece W} [Fintype ι] [Nontrivial ι]
    (J : JoinTree F)
    (hAntichain :
      ∀ ⦃i j : ι⦄, i ≠ j →
        ¬ (F i).carrier ⊆ (F j).carrier) :
    ∃ leaf parent : ι,
      J.tree.Adj leaf parent ∧
      (∀ j : ι, J.tree.Adj leaf j → j = parent) ∧
      ∃ x : W, x ∈ (F leaf).carrier ∧
        ∀ j : ι, j ≠ leaf → x ∉ (F j).carrier := by
  classical
  obtain ⟨leaf, parent, hadj, huniq, _⟩ :=
    J.exists_leaf_attachment
  have hNotSubset :
      ¬ (F leaf).carrier ⊆ (F parent).carrier :=
    hAntichain hadj.ne
  have hPrivate :
      ∃ x : W,
        x ∈ (F leaf).carrier ∧
        x ∉ (F parent).carrier := by
    by_contra h
    push_neg at h
    apply hNotSubset
    intro x hx
    exact h x hx
  obtain ⟨x, hxLeaf, hxNotParent⟩ := hPrivate
  refine ⟨leaf, parent, hadj, huniq, x, hxLeaf, ?_⟩
  intro j hj hxj
  exact hxNotParent
    (J.mem_parent_of_mem_leaf_and_other
      hadj huniq hj hxLeaf hxj)

/-- The carriers of an inclusion-antichain of nonempty join-tree bags
admit distinct representatives, each lying in the corresponding bag.
No bound on pairwise intersections is needed. -/
theorem JoinTree.exists_injective_representatives
    {F : ι → HypergraphPiece W} [Fintype ι] [Nonempty ι]
    (J : JoinTree F)
    (hNonempty : ∀ i : ι, (F i).carrier.Nonempty)
    (hAntichain :
      ∀ ⦃i j : ι⦄, i ≠ j →
        ¬ (F i).carrier ⊆ (F j).carrier) :
    ∃ f : ι → W,
      Function.Injective f ∧
      ∀ i : ι, f i ∈ (F i).carrier := by
  classical
  by_cases hsub : Subsingleton ι
  · let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    obtain ⟨x, hx⟩ := hNonempty i₀
    let f : ι → W := fun _ => x
    refine ⟨f, ?_, ?_⟩
    · intro i j _
      exact Subsingleton.elim i j
    · intro i
      have hi : i = i₀ := Subsingleton.elim i i₀
      simpa [f, hi] using hx
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, x, hxLeaf, hxPrivate⟩ :=
      J.exists_leaf_private_vertex hAntichain
    let reindexRest :
        {j : ι // j ≠ leaf} ≃
          {j : ι // j ∈ (({leaf} : Set ι)ᶜ)} :=
      Equiv.subtypeEquivRight (fun j => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let JRest :
        JoinTree (fun j : {t : ι // t ≠ leaf} => F j.1) := by
      simpa [erasePiece, reindexRest] using
        (J.eraseLeaf hadj huniq).reindex reindexRest
    have hNonemptyRest :
        ∀ j : {t : ι // t ≠ leaf},
          (F j.1).carrier.Nonempty :=
      fun j => hNonempty j.1
    have hAntichainRest :
        ∀ ⦃i j : {t : ι // t ≠ leaf}⦄, i ≠ j →
          ¬ (F i.1).carrier ⊆ (F j.1).carrier := by
      intro i j hij
      apply hAntichain
      intro heq
      apply hij
      exact Subtype.ext heq
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
    obtain ⟨fRest, hInjRest, hMemRest⟩ :=
      JoinTree.exists_injective_representatives
        JRest hNonemptyRest hAntichainRest
    let f : ι → W :=
      fun i => if h : i = leaf then x else fRest ⟨i, h⟩
    have hInjective : Function.Injective f := by
      intro i j hij
      by_cases hi : i = leaf
      · by_cases hj : j = leaf
        · exact hi.trans hj.symm
        · exfalso
          have hfi : f i = x := by simp [f, hi]
          have hfj : f j = fRest ⟨j, hj⟩ := by simp [f, hj]
          have hmemj : f j ∈ (F j).carrier := by
            rw [hfj]
            exact hMemRest ⟨j, hj⟩
          have hxj : x ∈ (F j).carrier := by
            have hxfj : x = f j := hfi.symm.trans hij
            simpa [hxfj] using hmemj
          exact hxPrivate j hj hxj
      · by_cases hj : j = leaf
        · exfalso
          have hfj : f j = x := by simp [f, hj]
          have hfi : f i = fRest ⟨i, hi⟩ := by simp [f, hi]
          have hmemi : f i ∈ (F i).carrier := by
            rw [hfi]
            exact hMemRest ⟨i, hi⟩
          have hfix : f i = x := hij.trans hfj
          have hxi : x ∈ (F i).carrier := by
            simpa [hfix] using hmemi
          exact hxPrivate i hi hxi
        · have hrest :
              fRest ⟨i, hi⟩ = fRest ⟨j, hj⟩ := by
            simpa [f, hi, hj] using hij
          exact congrArg Subtype.val (hInjRest hrest)
    refine ⟨f, hInjective, ?_⟩
    intro i
    by_cases hi : i = leaf
    · subst i
      simpa [f] using hxLeaf
    · have hfi : f i = fRest ⟨i, hi⟩ := by simp [f, hi]
      rw [hfi]
      exact hMemRest ⟨i, hi⟩
termination_by Fintype.card ι
decreasing_by
  exact hcard

/-- In particular the number of nonempty incomparable bags in a finite
join tree never exceeds the number of vertices they use. -/
theorem JoinTree.card_le_of_antichain
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι] [Fintype W]
    (J : JoinTree F)
    (hNonempty : ∀ i : ι, (F i).carrier.Nonempty)
    (hAntichain :
      ∀ ⦃i j : ι⦄, i ≠ j →
        ¬ (F i).carrier ⊆ (F j).carrier) :
    Fintype.card ι ≤ Fintype.card W := by
  obtain ⟨f, hf, _⟩ :=
    J.exists_injective_representatives hNonempty hAntichain
  exact Fintype.card_le_of_injective f hf

end StructuralRamsey.Girth
