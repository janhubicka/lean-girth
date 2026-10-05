import Girth.MixedFamilyUnion
import Girth.RelationalUnionFreeAmalgam

/-! # One leaf step for a mixed A/B forest

A leaf may itself be an A-copy or a B-copy.  In either case it embeds into one
fresh B-copy: use the fixed A -> B embedding for an A-leaf and the identity for
a B-leaf.  The separator is then handled uniformly as an A-copy, a supported
point, or the empty structure.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι X : Type v}

/-- Extend an embedding of the leaf-deleted mixed union across one leaf. -/
theorem ASupportedTreeAmalgam.extendMixedForestLeaf
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {m : ι → ABMember A B R}
    (J : JoinTree (fun i => (m i).supportPiece A))
    (hAllowed : PairwiseAllowed (fun i => (m i).supportPiece A))
    (hShared : PairwiseMixedSharedVerticesSupported A m)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    {T : RelStructure L X}
    (hT : ASupportedTreeAmalgam A B X T)
    (eRest :
      Embedding
        (mixedFamilyUnionStructure R
          (fun j : {j : ι // j ≠ leaf} => m j.1))
        T)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (Y : Type v) (S : RelStructure L Y)
        (e : Embedding (mixedFamilyUnionStructure R m) S),
      ASupportedTreeAmalgam A B Y S := by
  classical
  let p : {j : ι // j ≠ leaf} :=
    ⟨parent, hadj.ne.symm⟩
  let leafToB : Embedding (m leaf).source B :=
    (m leaf).toB alphaB
  rcases hAllowed hadj.ne with hSmall | hEdge
  · have hSmall' :
        ((m leaf).carrier ∩ (m parent).carrier).Subsingleton := by
      simpa using hSmall
    by_cases hEmpty :
        (m leaf).carrier ∩ (m parent).carrier = ∅
    · let D : RelStructure L PEmpty := ambientEmpty R
      let fRest :
          Embedding D
            (mixedFamilyUnionStructure R
              (fun j : {j : ι // j ≠ leaf} => m j.1)) :=
        (mixedMemberEmbedding
          (fun j : {j : ι // j ≠ leaf} => m j.1) p).comp
            (ambientEmptyToMember (m parent).toAmbient)
      let fLeaf : Embedding D (m leaf).source :=
        ambientEmptyToMember (m leaf).toAmbient
      have hOverlap :
          ∀ q :
              mixedFamilyCarrier
                (fun j : {j : ι // j ≠ leaf} => m j.1),
            ∀ y : (m leaf).VertexType,
              q.1 = (m leaf).toAmbient y ↔
                ∃ d : PEmpty, q = fRest d ∧ y = fLeaf d := by
        intro q y
        constructor
        · intro hqy
          have hBoth :
              q.1 ∈
                (m leaf).carrier ∩
                  mixedFamilyCarrier
                    (fun j : {j : ι // j ≠ leaf} => m j.1) :=
            ⟨⟨y, hqy.symm⟩, q.2⟩
          rw [J.mixed_leaf_inter_rest_eq_parent hadj huniq] at hBoth
          have hempty : q.1 ∈ (∅ : Set W) := by
            rw [← hEmpty]
            exact hBoth
          exfalso
          simpa using hempty
        · rintro ⟨d, _hq, _hy⟩
          exact PEmpty.elim d
      have hSrc :
          IsFreeAmalgam
            fRest fLeaf
            (J.mixedRestToFullEmbedding hadj huniq)
            (mixedMemberEmbedding m leaf) :=
        J.mixedFamilyUnion_isFreeAmalgam_leaf_of_overlap
          hadj huniq D fRest fLeaf hOverlap
      let alphaT : Embedding A T :=
        Classical.choice (hT.exists_aEmbedding alphaB)
      obtain ⟨Y, S, hS, iT, iB, hDisj, hSplit⟩ :=
        hT.exists_disjointCopyExtension_split
          alphaT alphaB a0 a1 hne
      let tRest : Embedding D T := eRest.comp fRest
      let tLeaf : Embedding D B := leafToB.comp fLeaf
      have hTgt :
          IsFreeAmalgam
            tRest tLeaf
            (leftToInducedImageUnion iT iB)
            (rightToInducedImageUnion iT iB) :=
        inducedImageUnion_isFreeAmalgam_of_disjoint
          tRest tLeaf iT iB hDisj hSplit
      let eInduced :
          Embedding
            (mixedFamilyUnionStructure R m)
            (S.induce (Set.range iT ∪ Set.range iB)) :=
        freeAmalgam_liftEmbedding_sameOverlap
          hSrc hTgt eRest leafToB
          (by intro d; exact PEmpty.elim d)
          (by intro d; exact PEmpty.elim d)
      let eFull : Embedding (mixedFamilyUnionStructure R m) S :=
        (induceToAmbient S (Set.range iT ∪ Set.range iB)).comp eInduced
      exact ⟨Y, S, eFull, hS⟩
    · have hNonempty :
          ((m leaf).carrier ∩ (m parent).carrier).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hEmpty
      rcases hNonempty with ⟨x, hx⟩
      have hEq :
          (m leaf).carrier ∩ (m parent).carrier = {x} := by
        apply Set.Subset.antisymm
        · intro y hy
          have hyx : y = x := hSmall' hy hx
          simpa [hyx]
        · intro y hy
          have hyx : y = x := by simpa using hy
          simpa [hyx] using hx
      have hs := hShared hadj.ne hx.1 hx.2
      rcases hs.1 with ⟨aLeaf, hxLeaf, hALeaf⟩
      rcases hs.2 with ⟨aParent, hxParent, hAParent⟩
      rcases hxLeaf with ⟨uLeaf, huLeaf⟩
      rcases hxParent with ⟨uParent, huParent⟩
      let alphaRest :
          Embedding A
            (mixedFamilyUnionStructure R
              (fun j : {j : ι // j ≠ leaf} => m j.1)) :=
        aCopyToMixedFamilyUnion
          (fun j : {j : ι // j ≠ leaf} => m j.1)
          aParent p hAParent
      let alphaLeaf : Embedding A (m leaf).source :=
        aCopyFactorIntoMixedMember
          (m leaf) aLeaf hALeaf
      let D : RelStructure L PUnit := ambientPoint R x
      let fRest :
          Embedding D
            (mixedFamilyUnionStructure R
              (fun j : {j : ι // j ≠ leaf} => m j.1)) :=
        ambientPointEmbedding
          aParent alphaRest uParent x huParent
      let fLeaf : Embedding D (m leaf).source :=
        ambientPointEmbedding
          aLeaf alphaLeaf uLeaf x huLeaf
      have hOverlap :
          ∀ q :
              mixedFamilyCarrier
                (fun j : {j : ι // j ≠ leaf} => m j.1),
            ∀ y : (m leaf).VertexType,
              q.1 = (m leaf).toAmbient y ↔
                ∃ d : PUnit, q = fRest d ∧ y = fLeaf d := by
        intro q y
        constructor
        · intro hqy
          have hBoth :
              q.1 ∈
                (m leaf).carrier ∩
                  mixedFamilyCarrier
                    (fun j : {j : ι // j ≠ leaf} => m j.1) :=
            ⟨⟨y, hqy.symm⟩, q.2⟩
          rw [J.mixed_leaf_inter_rest_eq_parent hadj huniq] at hBoth
          have hqx : q.1 = x := by
            have : q.1 ∈ ({x} : Set W) := by
              rw [← hEq]
              exact hBoth
            simpa using this
          refine ⟨PUnit.unit, ?_, ?_⟩
          · apply Subtype.ext
            change q.1 = aParent uParent
            exact hqx.trans huParent.symm
          · apply (m leaf).toAmbient.injective
            change
              (m leaf).toAmbient y =
                (m leaf).toAmbient (alphaLeaf uLeaf)
            calc
              (m leaf).toAmbient y = q.1 := hqy.symm
              _ = x := hqx
              _ = aLeaf uLeaf := huLeaf.symm
              _ = (m leaf).toAmbient (alphaLeaf uLeaf) := by
                exact
                  (aCopyFactorIntoMixedMember_spec
                    (m leaf) aLeaf hALeaf uLeaf).symm
        · rintro ⟨d, hq, hy⟩
          cases d
          have hqv : q.1 = aParent uParent := by
            exact congrArg Subtype.val hq
          have hyv :
              (m leaf).toAmbient y =
                (m leaf).toAmbient (alphaLeaf uLeaf) :=
            congrArg (m leaf).toAmbient hy
          calc
            q.1 = aParent uParent := hqv
            _ = x := huParent
            _ = aLeaf uLeaf := huLeaf.symm
            _ = (m leaf).toAmbient (alphaLeaf uLeaf) := by
              exact
                (aCopyFactorIntoMixedMember_spec
                  (m leaf) aLeaf hALeaf uLeaf).symm
            _ = (m leaf).toAmbient y := hyv.symm
      have hSrc :
          IsFreeAmalgam
            fRest fLeaf
            (J.mixedRestToFullEmbedding hadj huniq)
            (mixedMemberEmbedding m leaf) :=
        J.mixedFamilyUnion_isFreeAmalgam_leaf_of_overlap
          hadj huniq D fRest fLeaf hOverlap
      let fT : Embedding D T := eRest.comp fRest
      let fB : Embedding D B := leafToB.comp fLeaf
      have supportT :
          ∃ alpha : Embedding A T,
            ∀ d, ∃ a, fT d = alpha a := by
        refine ⟨eRest.comp alphaRest, ?_⟩
        intro d
        cases d
        exact ⟨uParent, rfl⟩
      have supportB :
          ∃ alpha : Embedding A B,
            ∀ d, ∃ a, fB d = alpha a := by
        refine ⟨leafToB.comp alphaLeaf, ?_⟩
        intro d
        cases d
        exact ⟨uLeaf, rfl⟩
      obtain ⟨Y, S, hS, iT, iB, hTgt⟩ :=
        hT.exists_freeGluePoint fT fB supportT supportB
      let eFull : Embedding (mixedFamilyUnionStructure R m) S :=
        freeAmalgam_liftEmbedding_sameOverlap
          hSrc hTgt eRest leafToB
          (by intro d; rfl)
          (by intro d; rfl)
      exact ⟨Y, S, eFull, hS⟩
  · rcases hEdge with ⟨e, heLeaf, _heParent, hInter⟩
    obtain ⟨a, ha, hALeaf⟩ :=
      (m leaf).supportEdge_witness A heLeaf
    have hInter' :
        (m leaf).carrier ∩ (m parent).carrier = e := by
      simpa using hInter
    have hAParent : copyCarrier a ⊆ (m parent).carrier := by
      intro z hz
      have hze : z ∈ e := by
        rw [← ha]
        exact hz
      have hzBoth :
          z ∈ (m leaf).carrier ∩ (m parent).carrier := by
        rw [hInter']
        exact hze
      exact hzBoth.2
    let fRest :
        Embedding A
          (mixedFamilyUnionStructure R
            (fun j : {j : ι // j ≠ leaf} => m j.1)) :=
      aCopyToMixedFamilyUnion
        (fun j : {j : ι // j ≠ leaf} => m j.1)
        a p hAParent
    let fLeaf : Embedding A (m leaf).source :=
      aCopyFactorIntoMixedMember (m leaf) a hALeaf
    have hOverlap :
        ∀ q :
            mixedFamilyCarrier
              (fun j : {j : ι // j ≠ leaf} => m j.1),
          ∀ y : (m leaf).VertexType,
            q.1 = (m leaf).toAmbient y ↔
              ∃ d : UA, q = fRest d ∧ y = fLeaf d := by
      intro q y
      constructor
      · intro hqy
        have hBoth :
            q.1 ∈
              (m leaf).carrier ∩
                mixedFamilyCarrier
                  (fun j : {j : ι // j ≠ leaf} => m j.1) :=
          ⟨⟨y, hqy.symm⟩, q.2⟩
        rw [J.mixed_leaf_inter_rest_eq_parent hadj huniq] at hBoth
        have hqa : q.1 ∈ copyCarrier a := by
          have hqe : q.1 ∈ e := by
            rw [← hInter']
            exact hBoth
          rw [ha]
          exact hqe
        rcases hqa with ⟨d, hd⟩
        refine ⟨d, ?_, ?_⟩
        · apply Subtype.ext
          exact hd.symm
        · apply (m leaf).toAmbient.injective
          calc
            (m leaf).toAmbient y = q.1 := hqy.symm
            _ = a d := hd.symm
            _ = (m leaf).toAmbient (fLeaf d) := by
              exact
                (aCopyFactorIntoMixedMember_spec
                  (m leaf) a hALeaf d).symm
      · rintro ⟨d, hq, hy⟩
        have hqv : q.1 = a d :=
          congrArg Subtype.val hq
        calc
          q.1 = a d := hqv
          _ = (m leaf).toAmbient (fLeaf d) := by
            exact
              (aCopyFactorIntoMixedMember_spec
                (m leaf) a hALeaf d).symm
          _ = (m leaf).toAmbient y :=
            congrArg (m leaf).toAmbient hy.symm
    have hSrc :
        IsFreeAmalgam
          fRest fLeaf
          (J.mixedRestToFullEmbedding hadj huniq)
          (mixedMemberEmbedding m leaf) :=
      J.mixedFamilyUnion_isFreeAmalgam_leaf_of_overlap
        hadj huniq A fRest fLeaf hOverlap
    let fT : Embedding A T := eRest.comp fRest
    let fB : Embedding A B := leafToB.comp fLeaf
    obtain ⟨Y, S, hS, iT, iB, hTgt⟩ :=
      hT.exists_freeGlueA fT fB
    let eFull : Embedding (mixedFamilyUnionStructure R m) S :=
      freeAmalgam_liftEmbedding_sameOverlap
        hSrc hTgt eRest leafToB
        (by intro d; rfl)
        (by intro d; rfl)
    exact ⟨Y, S, eFull, hS⟩

end StructuralRamsey.Girth
