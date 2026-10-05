import Girth.SupportedCopyForest

/-! # One recursive forest-to-supported-tree step

This module starts the leaf induction converting a relational union of
B-copies into an A-supported tree amalgam.  The first case is an exact A-copy
separator between the leaf and its parent.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι X : Type v}

/-- If a leaf meets its parent exactly in an A-copy, an embedding of the
leaf-deleted union into an A-supported tree amalgam extends across the leaf by
one canonical free A-gluing. -/
theorem ASupportedTreeAmalgam.extendCopyForestLeaf_overA
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    (J : BCopyJoinTree b)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (a : Embedding A R)
    (hInter :
      copyCarrier (b leaf) ∩ copyCarrier (b parent) =
        copyCarrier a)
    {T : RelStructure L X}
    (hT : ASupportedTreeAmalgam A B X T)
    (eRest :
      Embedding
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1))
        T) :
    ∃ (Y : Type v) (S : RelStructure L Y),
      ASupportedTreeAmalgam A B Y S ∧
      Embedding (familyUnionStructure R b) S := by
  classical
  let p : {j : ι // j ≠ leaf} :=
    ⟨parent, hadj.ne.symm⟩
  have hAParent :
      copyCarrier a ⊆ copyCarrier (b parent) := by
    intro z hz
    have hz' :
        z ∈ copyCarrier (b leaf) ∩ copyCarrier (b parent) := by
      rw [hInter]
      exact hz
    exact hz'.2
  have hALeaf :
      copyCarrier a ⊆ copyCarrier (b leaf) := by
    intro z hz
    have hz' :
        z ∈ copyCarrier (b leaf) ∩ copyCarrier (b parent) := by
      rw [hInter]
      exact hz
    exact hz'.1
  let fRest :
      Embedding A
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1)) :=
    aCopyToFamilyUnion
      (fun j : {j : ι // j ≠ leaf} => b j.1)
      a p hAParent
  let fLeaf : Embedding A B :=
    aCopyFactorIntoMember a (b leaf) hALeaf
  have hOverlap :
      ∀ q :
          familyCarrier
            (fun j : {j : ι // j ≠ leaf} => b j.1),
        ∀ y : VB,
          q.1 = b leaf y ↔
            ∃ d : UA, q = fRest d ∧ y = fLeaf d := by
    intro q y
    constructor
    · intro hqy
      have hBoth :
          q.1 ∈
            copyCarrier (b leaf) ∩
              familyCarrier
                (fun j : {j : ι // j ≠ leaf} => b j.1) :=
        ⟨⟨y, hqy.symm⟩, q.2⟩
      rw [J.leaf_inter_rest_eq_parent hadj huniq] at hBoth
      have hqa : q.1 ∈ copyCarrier a := by
        rw [← hInter]
        exact hBoth
      rcases hqa with ⟨d, hd⟩
      refine ⟨d, ?_, ?_⟩
      · apply Subtype.ext
        exact hd.symm
      · apply (b leaf).injective
        calc
          b leaf y = q.1 := hqy.symm
          _ = a d := hd.symm
          _ = b leaf (fLeaf d) := by
            exact (aCopyFactorIntoMember_spec a (b leaf) hALeaf d).symm
    · rintro ⟨d, hq, hy⟩
      have hqv :
          q.1 = a d := by
        have := congrArg Subtype.val hq
        exact this
      calc
        q.1 = a d := hqv
        _ = b leaf (fLeaf d) := by
          exact (aCopyFactorIntoMember_spec a (b leaf) hALeaf d).symm
        _ = b leaf y := congrArg (b leaf) hy.symm
  have hSrc :
      IsFreeAmalgam
        fRest fLeaf
        (J.restToFullEmbedding hadj huniq)
        (familyMemberEmbedding b leaf) :=
    J.familyUnion_isFreeAmalgam_leaf_of_overlap
      hadj huniq A fRest fLeaf hOverlap
  let fT : Embedding A T := eRest.comp fRest
  obtain ⟨Y, S, hS, iT, iB, hTgt⟩ :=
    hT.exists_freeGlueA fT fLeaf
  let idB : Embedding B B := (Iso.refl B).toEmbedding
  let eFull : Embedding (familyUnionStructure R b) S :=
    freeAmalgam_liftEmbedding_sameOverlap
      hSrc hTgt eRest idB
      (by intro d; rfl)
      (by intro d; rfl)
  exact ⟨Y, S, hS, eFull⟩

end StructuralRamsey.Girth
