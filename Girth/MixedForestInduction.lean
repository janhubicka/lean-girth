import Girth.MixedForestStep
import Girth.ForestLeafDeletion

/-! # Mixed forest induction

This is the direct formal counterpart of the manuscript observation converting
a forest of A- and B-copies into an A-supported tree amalgam.  No preliminary
replacement of A-members is needed: each leaf is realized in one fresh B-copy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι : Type v}

/-- A nonempty finite mixed join-tree family with allowed support intersections
and supported shared vertices embeds into an A-supported tree amalgam. -/
theorem mixedJoinTree_embeds_supportedTree
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {m : ι → ABMember A B R}
    [Fintype ι] [Nonempty ι]
    (J : JoinTree (fun i => (m i).supportPiece A))
    (hAllowed : PairwiseAllowed (fun i => (m i).supportPiece A))
    (hShared : PairwiseMixedSharedVerticesSupported A m)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (T : RelStructure L X),
      ASupportedTreeAmalgam A B X T ∧
      Embedding (mixedFamilyUnionStructure R m) T := by
  classical
  by_cases hsub : Subsingleton ι
  · let i : ι := Classical.choice (inferInstance : Nonempty ι)
    let eMember :
        Embedding (mixedFamilyUnionStructure R m) (m i).source :=
      mixedFamilyUnionToMember_of_subsingleton m i
    let eB : Embedding (mixedFamilyUnionStructure R m) B :=
      ((m i).toB alphaB).comp eMember
    exact
      ⟨VB, B, ASupportedTreeAmalgam.copy (Iso.refl B), eB⟩
  · letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _hLeafInter⟩ :=
      J.exists_leaf_attachment
    let p : {j : ι // j ≠ leaf} :=
      ⟨parent, hadj.ne.symm⟩
    let JRest :
        JoinTree
          (fun j : {j : ι // j ≠ leaf} =>
            (m j.1).supportPiece A) := by
      simpa [erasePiece, Set.mem_compl_iff, Set.mem_singleton_iff] using
        (J.eraseLeaf hadj huniq)
    have hAllowedRest :
        PairwiseAllowed
          (fun j : {j : ι // j ≠ leaf} =>
            (m j.1).supportPiece A) := by
      simpa [erasePiece, Set.mem_compl_iff, Set.mem_singleton_iff] using
        (JoinTree.pairwiseAllowed_erase hAllowed leaf)
    have hSharedRest :
        PairwiseMixedSharedVerticesSupported A
          (fun j : {j : ι // j ≠ leaf} => m j.1) :=
      pairwiseMixedSharedVerticesSupported_erase A hShared leaf
    letI : Nonempty {j : ι // j ≠ leaf} := ⟨p⟩
    have hcard :
        Fintype.card {j : ι // j ≠ leaf} < Fintype.card ι := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun j : {j : ι // j ≠ leaf} => j.1)
        Subtype.val_injective
      intro hsurj
      obtain ⟨j, hj⟩ := hsurj leaf
      exact j.2 hj
    obtain ⟨X, T, hT, eRest⟩ :=
      mixedJoinTree_embeds_supportedTree
        (ι := {j : ι // j ≠ leaf})
        JRest hAllowedRest hSharedRest alphaB a0 a1 hne
    obtain ⟨Y, S, hS, eFull⟩ :=
      hT.extendMixedForestLeaf
        J hAllowed hShared hadj huniq
        eRest alphaB a0 a1 hne
    exact ⟨Y, S, hS, eFull⟩
termination_by Fintype.card ι
decreasing_by
  exact hcard

/-- Forest-form wrapper of the mixed join-tree induction. -/
theorem mixedForest_embeds_supportedTree
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {m : ι → ABMember A B R}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies (fun i => (m i).supportPiece A))
    (hShared : PairwiseMixedSharedVerticesSupported A m)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (T : RelStructure L X),
      ASupportedTreeAmalgam A B X T ∧
      Embedding (mixedFamilyUnionStructure R m) T := by
  obtain ⟨J⟩ := hForest.joinTree_of_nonempty
  exact
    mixedJoinTree_embeds_supportedTree
      J hForest.pairwiseAllowed hShared alphaB a0 a1 hne

end StructuralRamsey.Girth
