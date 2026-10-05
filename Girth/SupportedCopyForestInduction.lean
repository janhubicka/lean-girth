import Girth.SupportedCopyForestStep
import Girth.ForestLeafDeletion

/-! # Leaf induction for supported B-copy forests

This completes the B-only core of the manuscript's conversion from a forest of
copies to an A-supported tree amalgam.  The proof recursively deletes a leaf,
embeds the remaining union, and applies the unified leaf-extension theorem.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι : Type v}

/-- A nonempty finite join-tree family of B-copies with the manuscript's
supported overlap trichotomy embeds into an A-supported tree amalgam. -/
theorem bCopyForest_embeds_supportedTree
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    [Fintype ι] [Nonempty ι]
    (J : BCopyJoinTree b)
    (hOverlap : PairwiseSupportedBCopyOverlap A b)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (T : RelStructure L X)
        (e : Embedding (familyUnionStructure R b) T),
      ASupportedTreeAmalgam A B X T := by
  classical
  by_cases hsub : Subsingleton ι
  · let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact
      ⟨VB, B, familyUnionToMember_of_subsingleton b i,
        ASupportedTreeAmalgam.copy (Iso.refl B)⟩
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _hLeafInter⟩ :=
      J.exists_leaf_attachment
    let p : {j : ι // j ≠ leaf} :=
      ⟨parent, hadj.ne.symm⟩
    let reindexRest :
        {j : ι // j ≠ leaf} ≃
          {j : ι // j ∈ (({leaf} : Set ι)ᶜ)} :=
      Equiv.subtypeEquivRight (fun j => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let JRest :
        BCopyJoinTree
          (fun j : {j : ι // j ≠ leaf} => b j.1) := by
      simpa [erasePiece, reindexRest] using
        (J.eraseLeaf hadj huniq).reindex reindexRest
    have hOverlapRest :
        PairwiseSupportedBCopyOverlap A
          (fun j : {j : ι // j ≠ leaf} => b j.1) :=
      pairwiseSupportedBCopyOverlap_erase A hOverlap leaf
    letI : Nonempty {j : ι // j ≠ leaf} := ⟨p⟩
    have hcard :
        Fintype.card {j : ι // j ≠ leaf} < Fintype.card ι := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun j : {j : ι // j ≠ leaf} => j.1)
        Subtype.val_injective
      intro hsurj
      obtain ⟨j, hj⟩ := hsurj leaf
      exact j.2 hj
    obtain ⟨X, T, eRest, hT⟩ :=
      bCopyForest_embeds_supportedTree
        (b := fun j : {j : ι // j ≠ leaf} => b j.1)
        JRest hOverlapRest alphaB a0 a1 hne
    obtain ⟨Y, S, eFull, hS⟩ :=
      hT.extendCopyForestLeaf
        J hOverlap hadj huniq eRest alphaB a0 a1 hne
    exact ⟨Y, S, eFull, hS⟩
termination_by Fintype.card ι
decreasing_by
  exact hcard

end StructuralRamsey.Girth
