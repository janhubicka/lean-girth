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

/-- If a leaf meets the rest in one supported vertex, the induction extends
across the leaf by one supported singleton gluing. -/
theorem ASupportedTreeAmalgam.extendCopyForestLeaf_overPoint
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    (J : BCopyJoinTree b)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (x : W)
    (hInter :
      copyCarrier (b leaf) ∩ copyCarrier (b parent) = {x})
    (hParent : VertexSupportedInBCopy A (b parent) x)
    (hLeaf : VertexSupportedInBCopy A (b leaf) x)
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
  rcases hParent with ⟨aParent, hxParent, hAParent⟩
  rcases hLeaf with ⟨aLeaf, hxLeaf, hALeaf⟩
  rcases hxParent with ⟨uParent, huParent⟩
  rcases hxLeaf with ⟨uLeaf, huLeaf⟩
  let alphaRest :
      Embedding A
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1)) :=
    aCopyToFamilyUnion
      (fun j : {j : ι // j ≠ leaf} => b j.1)
      aParent p hAParent
  let alphaLeaf : Embedding A B :=
    aCopyFactorIntoMember aLeaf (b leaf) hALeaf
  let D : RelStructure L PUnit := ambientPoint R x
  let fRest :
      Embedding D
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1)) :=
    ambientPointEmbedding
      aParent alphaRest uParent x huParent
  let fLeaf : Embedding D B :=
    ambientPointEmbedding
      aLeaf alphaLeaf uLeaf x huLeaf
  have hOverlap :
      ∀ q :
          familyCarrier
            (fun j : {j : ι // j ≠ leaf} => b j.1),
        ∀ y : VB,
          q.1 = b leaf y ↔
            ∃ d : PUnit, q = fRest d ∧ y = fLeaf d := by
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
      have hqx : q.1 = x := by
        have : q.1 ∈ ({x} : Set W) := by
          rw [← hInter]
          exact hBoth
        simpa using this
      refine ⟨PUnit.unit, ?_, ?_⟩
      · apply Subtype.ext
        change q.1 = aParent uParent
        exact hqx.trans huParent.symm
      · apply (b leaf).injective
        change b leaf y = b leaf (alphaLeaf uLeaf)
        calc
          b leaf y = q.1 := hqy.symm
          _ = x := hqx
          _ = aLeaf uLeaf := huLeaf.symm
          _ = b leaf (alphaLeaf uLeaf) := by
            exact
              (aCopyFactorIntoMember_spec
                aLeaf (b leaf) hALeaf uLeaf).symm
    · rintro ⟨d, hq, hy⟩
      cases d
      have hqv :
          q.1 = aParent uParent := by
        have := congrArg Subtype.val hq
        exact this
      have hyb :
          b leaf y = b leaf (alphaLeaf uLeaf) := by
        exact congrArg (b leaf) hy
      calc
        q.1 = aParent uParent := hqv
        _ = x := huParent
        _ = aLeaf uLeaf := huLeaf.symm
        _ = b leaf (alphaLeaf uLeaf) := by
          exact
            (aCopyFactorIntoMember_spec
              aLeaf (b leaf) hALeaf uLeaf).symm
        _ = b leaf y := hyb.symm
  have hSrc :
      IsFreeAmalgam
        fRest fLeaf
        (J.restToFullEmbedding hadj huniq)
        (familyMemberEmbedding b leaf) :=
    J.familyUnion_isFreeAmalgam_leaf_of_overlap
      hadj huniq D fRest fLeaf hOverlap
  let fT : Embedding D T := eRest.comp fRest
  have supportT :
      ∃ alpha : Embedding A T,
        ∀ d, ∃ a, fT d = alpha a := by
    refine ⟨eRest.comp alphaRest, ?_⟩
    intro d
    cases d
    exact ⟨uParent, rfl⟩
  have supportB :
      ∃ alpha : Embedding A B,
        ∀ d, ∃ a, fLeaf d = alpha a := by
    refine ⟨alphaLeaf, ?_⟩
    intro d
    cases d
    exact ⟨uLeaf, rfl⟩
  obtain ⟨Y, S, hS, iT, iB, hTgt⟩ :=
    hT.exists_freeGluePoint fT fLeaf supportT supportB
  let idB : Embedding B B := (Iso.refl B).toEmbedding
  let eFull : Embedding (familyUnionStructure R b) S :=
    freeAmalgam_liftEmbedding_sameOverlap
      hSrc hTgt eRest idB
      (by intro d; rfl)
      (by intro d; rfl)
  exact ⟨Y, S, hS, eFull⟩

/-- If a leaf is disjoint from its parent, then it is disjoint from the whole
leaf-deleted union.  Three supported singleton bridge gluings place a fresh
B-copy far enough from the old target that the two source sides remain both
vertex-disjoint and relation-separated. -/
theorem ASupportedTreeAmalgam.extendCopyForestLeaf_overEmpty
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    (J : BCopyJoinTree b)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (hInter :
      copyCarrier (b leaf) ∩ copyCarrier (b parent) = ∅)
    {T : RelStructure L X}
    (hT : ASupportedTreeAmalgam A B X T)
    (eRest :
      Embedding
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1))
        T)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (Y : Type v) (S : RelStructure L Y),
      ASupportedTreeAmalgam A B Y S ∧
      Embedding (familyUnionStructure R b) S := by
  classical
  let p : {j : ι // j ≠ leaf} :=
    ⟨parent, hadj.ne.symm⟩
  let D : RelStructure L PEmpty := ambientEmpty R
  let fRest :
      Embedding D
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1)) :=
    ambientEmptyToFamilyUnion
      (fun j : {j : ι // j ≠ leaf} => b j.1) p
  let fLeaf : Embedding D B :=
    ambientEmptyToMember (b leaf)
  have hOverlap :
      ∀ q :
          familyCarrier
            (fun j : {j : ι // j ≠ leaf} => b j.1),
        ∀ y : VB,
          q.1 = b leaf y ↔
            ∃ d : PEmpty, q = fRest d ∧ y = fLeaf d := by
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
      have hempty : q.1 ∈ (∅ : Set W) := by
        rw [← hInter]
        exact hBoth
      exfalso
      simpa using hempty
    · rintro ⟨d, _hq, _hy⟩
      exact PEmpty.elim d
  have hSrc :
      IsFreeAmalgam
        fRest fLeaf
        (J.restToFullEmbedding hadj huniq)
        (familyMemberEmbedding b leaf) :=
    J.familyUnion_isFreeAmalgam_leaf_of_overlap
      hadj huniq D fRest fLeaf hOverlap
  obtain ⟨Y, S, hS, iT, iB, hDisj, hSplit⟩ :=
    hT.exists_disjointCopyExtension_split
      (Classical.choice (hT.exists_aEmbedding alphaB))
      alphaB a0 a1 hne
  have hTgt :
      IsFreeAmalgam
        (eRest.comp fRest) fLeaf
        (leftToInducedImageUnion iT iB)
        (rightToInducedImageUnion iT iB) :=
    inducedImageUnion_isFreeAmalgam_of_disjoint
      (eRest.comp fRest) fLeaf iT iB hDisj hSplit
  let idB : Embedding B B := (Iso.refl B).toEmbedding
  let eInduced :
      Embedding
        (familyUnionStructure R b)
        (S.induce (Set.range iT ∪ Set.range iB)) :=
    freeAmalgam_liftEmbedding_sameOverlap
      hSrc hTgt eRest idB
      (by intro d; exact PEmpty.elim d)
      (by intro d; exact PEmpty.elim d)
  let eFull : Embedding (familyUnionStructure R b) S :=
    (induceToAmbient S (Set.range iT ∪ Set.range iB)).comp eInduced
  exact ⟨Y, S, hS, eFull⟩

/-- Unified recursive leaf step.  The supported-overlap trichotomy is exactly
the case split needed by the forest-to-tree-amalgam induction. -/
theorem ASupportedTreeAmalgam.extendCopyForestLeaf
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    (J : BCopyJoinTree b)
    (hOverlap : PairwiseSupportedBCopyOverlap A b)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    {T : RelStructure L X}
    (hT : ASupportedTreeAmalgam A B X T)
    (eRest :
      Embedding
        (familyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => b j.1))
        T)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (Y : Type v) (S : RelStructure L Y),
      ASupportedTreeAmalgam A B Y S ∧
      Embedding (familyUnionStructure R b) S := by
  rcases hOverlap hadj.ne with hEmpty | hCopy | hPoint
  · exact
      hT.extendCopyForestLeaf_overEmpty
        J hadj huniq hEmpty eRest alphaB a0 a1 hne
  · rcases hCopy with ⟨a, ha⟩
    exact hT.extendCopyForestLeaf_overA J hadj huniq a ha eRest
  · rcases hPoint with ⟨x, hx, hsLeaf, hsParent⟩
    exact
      hT.extendCopyForestLeaf_overPoint
        J hadj huniq x hx hsParent hsLeaf eRest

end StructuralRamsey.Girth
