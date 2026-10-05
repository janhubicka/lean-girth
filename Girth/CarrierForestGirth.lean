import Girth.ForestLeafDeletion
import Girth.BergeGlue

/-! # Berge girth of carrier forests

A finite family with a join tree and pairwise subsingleton carrier
intersections is Berge-acyclic.  This is the abstract combinatorial core of
the manuscript's observation that a forest restricted to one part has no
Berge cycle.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Hypergraph whose edges are exactly the carriers of a labelled family of
pieces. -/
def carrierEdgeFamily (F : ι → HypergraphPiece W) : Set (Set W) :=
  {e | ∃ i : ι, e = (F i).carrier}

/-- The carrier edge family of a finite join tree with pairwise subsingleton
intersections has girth above every prescribed finite bound. -/
theorem girthGT_carrierEdgeFamily_of_joinTree
    {ι : Type v}
    {F : ι → HypergraphPiece W}
    [Fintype ι] [Nonempty ι]
    (J : JoinTree F)
    (hPair :
      ∀ ⦃i j : ι⦄, i ≠ j →
        ((F i).carrier ∩ (F j).carrier).Subsingleton)
    (g : ℕ) :
    GirthGT (carrierEdgeFamily F) g := by
  classical
  by_cases hsub : Subsingleton ι
  · apply girthGT_of_edgeFamily_subsingleton
    intro E hE G hG
    rcases hE with ⟨i, rfl⟩
    rcases hG with ⟨j, rfl⟩
    have hij : i = j := Subsingleton.elim _ _
    simpa [hij]
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _hInter⟩ :=
      J.exists_leaf_attachment
    let p : {j : ι // j ≠ leaf} :=
      ⟨parent, hadj.ne.symm⟩
    let reindexRest :
        {j : ι // j ≠ leaf} ≃
          {j : ι // j ∈ (({leaf} : Set ι)ᶜ)} :=
      Equiv.subtypeEquivRight (fun j => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let FRest : {j : ι // j ≠ leaf} → HypergraphPiece W :=
      fun j => F j.1
    let JRest : JoinTree FRest := by
      simpa [FRest, erasePiece, reindexRest] using
        (J.eraseLeaf hadj huniq).reindex reindexRest
    have hPairRest :
        ∀ ⦃i j : {j : ι // j ≠ leaf}⦄, i ≠ j →
          ((FRest i).carrier ∩ (FRest j).carrier).Subsingleton := by
      intro i j hij
      apply hPair
      intro hval
      apply hij
      exact Subtype.ext hval
    letI : Nonempty {j : ι // j ≠ leaf} := ⟨p⟩
    have hcard :
        Fintype.card {j : ι // j ≠ leaf} < Fintype.card ι := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun j : {j : ι // j ≠ leaf} => j.1)
        Subtype.val_injective
      intro hsurj
      obtain ⟨j, hj⟩ := hsurj leaf
      exact j.2 hj
    have hRest :
        GirthGT (carrierEdgeFamily FRest) g :=
      girthGT_carrierEdgeFamily_of_joinTree
        (ι := {j : ι // j ≠ leaf})
        JRest hPairRest g
    let HL : Set (Set W) := {(F leaf).carrier}
    let S : Set W := (F leaf).carrier ∩ (F parent).carrier
    have hS : S.Subsingleton := by
      exact hPair hadj.ne
    have hL : GirthGT HL g := by
      apply girthGT_of_edgeFamily_subsingleton
      intro E hE G hG
      simpa [HL] using hE.trans hG.symm
    have hcross :
        ∀ ⦃eL eR : Set W⦄,
          eL ∈ HL →
          eR ∈ carrierEdgeFamily FRest →
          eL ∩ eR ⊆ S := by
      intro eL eR heL heR x hx
      have heL' : eL = (F leaf).carrier := by
        simpa [HL] using heL
      rcases heR with ⟨j, heR'⟩
      have hxLeaf : x ∈ (F leaf).carrier := by
        simpa [heL'] using hx.1
      have hxJ : x ∈ (F j.1).carrier := by
        simpa [FRest, heR'] using hx.2
      have hxParent :
          x ∈ (F parent).carrier :=
        J.mem_parent_of_mem_leaf_and_other
          hadj huniq j.2 hxLeaf hxJ
      exact ⟨hxLeaf, hxParent⟩
    have hUnion :
        GirthGT (HL ∪ carrierEdgeFamily FRest) g :=
      girthGT_union_of_subsingleton_glue
        hS hcross hL hRest
    have hEq :
        carrierEdgeFamily F =
          HL ∪ carrierEdgeFamily FRest := by
      ext E
      constructor
      · rintro ⟨i, rfl⟩
        by_cases hil : i = leaf
        · subst i
          exact Or.inl (by simp [HL])
        · exact Or.inr ⟨⟨i, hil⟩, rfl⟩
      · intro h
        rcases h with hLeaf | hRestMem
        · have hE : E = (F leaf).carrier := by
            simpa [HL] using hLeaf
          exact ⟨leaf, hE⟩
        · rcases hRestMem with ⟨j, hj⟩
          exact ⟨j.1, by simpa [FRest] using hj⟩
    rw [hEq]
    exact hUnion
termination_by Fintype.card ι
decreasing_by
  exact hcard

end StructuralRamsey.Girth
