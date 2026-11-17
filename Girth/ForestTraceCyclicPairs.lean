import Girth.ForestLeafDeletion

/-!
# Cyclic pairs cannot be covered by a join-tree family

A reusable nonchordality obstruction: a finite family of required
vertex pairs has a cycle-like incidence pattern (each endpoint
appears in a second required pair). If no bag may cover two distinct
required pairs, the pairs cannot all be covered by bags that admit
a running-intersection join tree.

The proof removes a leaf of the join tree. A pair formerly covered
by this leaf is still covered by the parent: each endpoint belongs
to another required pair, whose witness is a different bag by the
no-double-coverage condition. Running intersection puts each
endpoint into the parent. Repeating yields one bag covering two
distinct required pairs, a contradiction.

This lemma will replace a generic graph-chordality library input
in the small-traces argument. Connecting a chordless cycle in the
trace pair graph to these data remains a separate, exact adapter.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι E : Type v}

/-- Cyclic required pairs cannot all be covered by an indexed
running-intersection family without some member covering two of
the pairs. No assumptions on support edges are necessary. -/
theorem JoinTree.no_cyclic_unique_pairs
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (J : JoinTree F)
    (a b : E → W)
    (e₀ e₁ : E) (he : e₀ ≠ e₁)
    (hOtherA :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = a e ∨ b f = a e))
    (hOtherB :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = b e ∨ b f = b e))
    (hPairs :
      ∀ e : E, ∃ i : ι,
        a e ∈ (F i).carrier ∧ b e ∈ (F i).carrier)
    (hUnique :
      ∀ i : ι, ∀ e f : E, e ≠ f →
        (a e ∈ (F i).carrier ∧ b e ∈ (F i).carrier) →
        (a f ∈ (F i).carrier ∧ b f ∈ (F i).carrier) → False) :
    False := by
  classical
  by_cases hsub : Subsingleton ι
  · letI : Subsingleton ι := hsub
    obtain ⟨i, hai, hbi⟩ := hPairs e₀
    obtain ⟨j, haj, hbj⟩ := hPairs e₁
    have hij : j = i := Subsingleton.elim j i
    exact hUnique i e₀ e₁ he ⟨hai, hbi⟩
      ⟨by simpa only [hij] using haj,
       by simpa only [hij] using hbj⟩
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _⟩ :=
      J.exists_leaf_attachment
    let reindexRest :
        {i : ι // i ≠ leaf} ≃
          {i : ι // i ∈ (({leaf} : Set ι)ᶜ)} :=
      Equiv.subtypeEquivRight (fun i => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let JRest :
        JoinTree (fun i : {t : ι // t ≠ leaf} => F i.1) := by
      simpa [erasePiece, reindexRest] using
        (J.eraseLeaf hadj huniq).reindex reindexRest
    letI : Nonempty {i : ι // i ≠ leaf} :=
      ⟨⟨parent, hadj.ne.symm⟩⟩
    have hUniqueRest :
        ∀ i : {t : ι // t ≠ leaf}, ∀ e f : E, e ≠ f →
          (a e ∈ (F i.1).carrier ∧ b e ∈ (F i.1).carrier) →
          (a f ∈ (F i.1).carrier ∧ b f ∈ (F i.1).carrier) → False := by
      intro i e f hef hePair hfPair
      exact hUnique i.1 e f hef hePair hfPair
    have hPairsRest :
        ∀ e : E, ∃ i : {t : ι // t ≠ leaf},
          a e ∈ (F i.1).carrier ∧ b e ∈ (F i.1).carrier := by
      intro e
      obtain ⟨i, hai, hbi⟩ := hPairs e
      by_cases hi : i = leaf
      · subst i
        obtain ⟨fa, hfaNe, hfaShare⟩ := hOtherA e
        obtain ⟨ia, haia, hbia⟩ := hPairs fa
        have hiaNe : ia ≠ leaf := by
          intro h
          subst ia
          exact hUnique leaf e fa hfaNe.symm
            ⟨hai, hbi⟩ ⟨haia, hbia⟩
        have haeInIa : a e ∈ (F ia).carrier := by
          rcases hfaShare with h | h
          · simpa only [h] using haia
          · simpa only [h] using hbia
        have haeParent : a e ∈ (F parent).carrier :=
          J.mem_parent_of_mem_leaf_and_other
            hadj huniq hiaNe hai haeInIa
        obtain ⟨fb, hfbNe, hfbShare⟩ := hOtherB e
        obtain ⟨ib, haib, hbib⟩ := hPairs fb
        have hibNe : ib ≠ leaf := by
          intro h
          subst ib
          exact hUnique leaf e fb hfbNe.symm
            ⟨hai, hbi⟩ ⟨haib, hbib⟩
        have hbeInIb : b e ∈ (F ib).carrier := by
          rcases hfbShare with h | h
          · simpa only [h] using haib
          · simpa only [h] using hbib
        have hbeParent : b e ∈ (F parent).carrier :=
          J.mem_parent_of_mem_leaf_and_other
            hadj huniq hibNe hbi hbeInIb
        exact ⟨⟨parent, hadj.ne.symm⟩, haeParent, hbeParent⟩
      · exact ⟨⟨i, hi⟩, hai, hbi⟩
    have hcard :
        Fintype.card {i : ι // i ≠ leaf} < Fintype.card ι := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun i : {t : ι // t ≠ leaf} => i.1)
        Subtype.val_injective
      intro hsurj
      obtain ⟨j, hj⟩ := hsurj leaf
      exact j.2 hj
    exact JoinTree.no_cyclic_unique_pairs
      JRest a b e₀ e₁ he hOtherA hOtherB
      hPairsRest hUniqueRest
termination_by Fintype.card ι
decreasing_by
  exact hcard

end StructuralRamsey.Girth
