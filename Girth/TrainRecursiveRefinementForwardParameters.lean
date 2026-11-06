import Girth.TrainRecursiveRefinementParameters

set_option autoImplicit false
set_option Elab.async false

/-!
# Forward adjacent-parameter transfer through a first-wagon refinement

Forgetting first-wagon cuts preserves the old parameters; the converse
requires care.  The inserted steps are controlled by the actual
FirstWagonRefinement.parameters certificates.  Every later fine
adjacent cut is a retained pair of adjacent ORIGINAL positive cuts,
whose labelled quotient carriers and parent maps are identical under
the checked forgetFirstCuts equivalences.

This theorem assembles those two disjoint cases.  The retained bounds
come from an actual original train AdjacentParameters proof; no
independent assumption of full fine AdjacentParameters is used.

The allowed sets are arbitrary actual vertex predicates.  In a
partite application, the inserted permitted sets are pulled back from
R.permitted and the retained ones from the old base allowed sets.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P : Type v}

/-- A physical parent-child intersection bound at a forgotten coarse
pair transports to the corresponding fine retained pair. This
holds even for nonadjacent coarse endpoints; parent maps and the
complete quotient-labelled carriers are exactly the same. -/
theorem EdgeTrainLevels.retainedParentBound_of_forgotten
    {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (allowedOld allowedNew : Set W)
    (hAllowed : allowedOld ⊆ allowedNew)
    (hOld : TrainParentIntersectionBound
      ((T.forgetFirstCuts hm).wagonClassCarrier edge μ)
      ((T.forgetFirstCuts hm).wagonParent μ ν hμν) allowedOld) :
    TrainParentIntersectionBound
      (T.wagonClassCarrier edge
        (EdgeTrainLevels.firstForgetIndex m d μ))
      (T.wagonParent
        (EdgeTrainLevels.firstForgetIndex m d μ)
        (EdgeTrainLevels.firstForgetIndex m d ν)
        (EdgeTrainLevels.firstForgetIndex_monotone m d hμν))
      allowedNew := by
  have hOldNew : TrainParentIntersectionBound
      ((T.forgetFirstCuts hm).wagonClassCarrier edge μ)
      ((T.forgetFirstCuts hm).wagonParent μ ν hμν) allowedNew := by
    intro a b hab hp x hx
    exact hAllowed (hOld hab hp hx)
  let child :
      Quotient (T.wagonSetoid (EdgeTrainLevels.firstForgetIndex m d μ)) ↪
      Quotient ((T.forgetFirstCuts hm).wagonSetoid μ) :=
    (T.forgetFirstCuts_wagonEquiv hm μ).symm.toEmbedding
  let parent :
      Quotient (T.wagonSetoid (EdgeTrainLevels.firstForgetIndex m d ν)) →
      Quotient ((T.forgetFirstCuts hm).wagonSetoid ν) :=
    (T.forgetFirstCuts_wagonEquiv hm ν).symm
  apply trainParentIntersectionBound_restrict
    ((T.forgetFirstCuts hm).wagonClassCarrier edge μ)
    ((T.forgetFirstCuts hm).wagonParent μ ν hμν)
    (T.wagonClassCarrier edge
      (EdgeTrainLevels.firstForgetIndex m d μ))
    (T.wagonParent (EdgeTrainLevels.firstForgetIndex m d μ)
      (EdgeTrainLevels.firstForgetIndex m d ν)
      (EdgeTrainLevels.firstForgetIndex_monotone m d hμν))
    allowedNew hOldNew child parent
  · intro a
    induction a using Quotient.inductionOn with
    | h a => rfl
  · intro a
    induction a using Quotient.inductionOn with
    | h a => exact Set.Subset.rfl

/-- The full fine train has all adjacent intersection parameters when
the old train has its original parameters and the genuine refinement
supplies its inserted ones. At a retained positive parent ν≥2 the
fine permitted set merely has to contain the corresponding old
allowed vertex set. The inserted sets merely contain the genuine
R.permitted fibre; no arbitrary fresh parameter hypothesis appears. -/
theorem FirstWagonRefinement.adjacentParameters_of_old
    {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P}
    {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (oldAllowed : Fin (m + 1) → Set W)
    (fineAllowed : Fin (m + R.extraCuts + 1) → Set W)
    (hOld : T.AdjacentParameters edge oldAllowed)
    (hInserted : ∀ j : Fin (R.extraCuts + 1),
      part ⁻¹' R.permitted j ⊆
        fineAllowed (firstRefinementParent m R.extraCuts hm j))
    (hRetained : ∀ ν : Fin (m + 1), 1 < ν.val →
      oldAllowed ν ⊆
        fineAllowed (EdgeTrainLevels.firstForgetIndex m R.extraCuts ν)) :
    R.train.AdjacentParameters edge fineAllowed := by
  classical
  intro μ ν hμν hNext a b hne hParent x hx
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      have hFineNe : ¬ R.train.rel μ a b := by
        intro hab
        exact hne (Quotient.sound hab)
      have hFineParent : R.train.rel ν a b := by
        change
          (Quotient.mk (R.train.wagonSetoid ν) a) =
            Quotient.mk (R.train.wagonSetoid ν) b at hParent
        exact Quotient.exact hParent
      have hxA : x ∈ R.train.wagonCarrier edge μ a := hx.1
      have hxB : x ∈ R.train.wagonCarrier edge μ b := hx.2
      by_cases hInsertedLevel : ν.val ≤ R.extraCuts + 1
      · let j : Fin (R.extraCuts + 1) := ⟨μ.val, by omega⟩
        have hμ :
            firstRefinementChild m R.extraCuts hm j = μ := by
          apply Fin.ext
          rfl
        have hν :
            firstRefinementParent m R.extraCuts hm j = ν := by
          apply Fin.ext
          change μ.val + 1 = ν.val
          omega
        have hChildNe :
            (Quotient.mk (R.train.wagonSetoid
              (firstRefinementChild m R.extraCuts hm j)) a :
              Quotient (R.train.wagonSetoid
                (firstRefinementChild m R.extraCuts hm j))) ≠
              Quotient.mk _ b := by
          intro heq
          apply hFineNe
          have hRel : R.train.rel
              (firstRefinementChild m R.extraCuts hm j) a b :=
            Quotient.exact heq
          simpa only [hμ] using hRel
        have hParentRel : R.train.rel
            (firstRefinementParent m R.extraCuts hm j) a b := by
          simpa only [hν] using hFineParent
        have hxChildA : x ∈ R.train.wagonCarrier edge
            (firstRefinementChild m R.extraCuts hm j) a := by
          simpa only [hμ] using hxA
        have hxChildB : x ∈ R.train.wagonCarrier edge
            (firstRefinementChild m R.extraCuts hm j) b := by
          simpa only [hμ] using hxB
        have hxPermitted : x ∈ part ⁻¹' R.permitted j :=
          R.parameters j hChildNe (Quotient.sound hParentRel)
            ⟨hxChildA, hxChildB⟩
        have hxFine : x ∈ fineAllowed
            (firstRefinementParent m R.extraCuts hm j) :=
          hInserted j hxPermitted
        simpa only [hν] using hxFine
      · have hμBig : R.extraCuts + 1 ≤ μ.val := by omega
        let μc : Fin (m + 1) := ⟨μ.val - R.extraCuts, by omega⟩
        let νc : Fin (m + 1) := ⟨ν.val - R.extraCuts, by omega⟩
        have hμPos : 0 < μc.val := by
          change 0 < μ.val - R.extraCuts
          omega
        have hνPos : 0 < νc.val := by
          change 0 < ν.val - R.extraCuts
          omega
        have hνTwo : 1 < νc.val := by
          change 1 < ν.val - R.extraCuts
          omega
        have hcc : μc ≤ νc := by
          change μ.val - R.extraCuts ≤ ν.val - R.extraCuts
          omega
        have hNextC : νc.val = μc.val + 1 := by
          change ν.val - R.extraCuts =
            μ.val - R.extraCuts + 1
          omega
        have hμEq :
            EdgeTrainLevels.firstForgetIndex m R.extraCuts μc = μ := by
          apply Fin.ext
          change (if μc.val = 0 then 0 else
            μc.val + R.extraCuts) = μ.val
          simp only [Nat.ne_of_gt hμPos, ↓reduceIte]
          change μ.val - R.extraCuts + R.extraCuts = μ.val
          omega
        have hνEq :
            EdgeTrainLevels.firstForgetIndex m R.extraCuts νc = ν := by
          apply Fin.ext
          change (if νc.val = 0 then 0 else
            νc.val + R.extraCuts) = ν.val
          simp only [Nat.ne_of_gt hνPos, ↓reduceIte]
          change ν.val - R.extraCuts + R.extraCuts = ν.val
          omega
        have hShiftμ :
            EdgeTrainLevels.firstRefinementShift
              m R.extraCuts μc = μ :=
          (EdgeTrainLevels.firstForgetIndex_of_pos
            m R.extraCuts μc hμPos).symm.trans hμEq
        have hShiftν :
            EdgeTrainLevels.firstRefinementShift
              m R.extraCuts νc = ν :=
          (EdgeTrainLevels.firstForgetIndex_of_pos
            m R.extraCuts νc hνPos).symm.trans hνEq
        have hOldNe :
            (Quotient.mk (T.wagonSetoid μc) a :
              Quotient (T.wagonSetoid μc)) ≠ Quotient.mk _ b := by
          intro heq
          have hRel : T.rel μc a b := Quotient.exact heq
          have hFine : R.train.rel
              (EdgeTrainLevels.firstRefinementShift
                m R.extraCuts μc) a b :=
            (R.oldLevels μc hμPos a b).mpr hRel
          exact hFineNe (by simpa only [hShiftμ] using hFine)
        have hOldParentRel : T.rel νc a b := by
          apply (R.oldLevels νc hνPos a b).mp
          simpa only [hShiftν] using hFineParent
        have hOldParent :
            T.wagonParent μc νc hcc
              (Quotient.mk (T.wagonSetoid μc) a) =
            T.wagonParent μc νc hcc
              (Quotient.mk (T.wagonSetoid μc) b) :=
          Quotient.sound hOldParentRel
        have hxOldA : x ∈ T.wagonCarrier edge μc a := by
          obtain ⟨c, hac, hxc⟩ := hxA
          have hFine : R.train.rel
              (EdgeTrainLevels.firstRefinementShift
                m R.extraCuts μc) a c := by
            simpa only [hShiftμ] using hac
          exact ⟨c, (R.oldLevels μc hμPos a c).mp hFine, hxc⟩
        have hxOldB : x ∈ T.wagonCarrier edge μc b := by
          obtain ⟨c, hbc, hxc⟩ := hxB
          have hFine : R.train.rel
              (EdgeTrainLevels.firstRefinementShift
                m R.extraCuts μc) b c := by
            simpa only [hShiftμ] using hbc
          exact ⟨c, (R.oldLevels μc hμPos b c).mp hFine, hxc⟩
        have hOldVertex : x ∈ oldAllowed νc :=
          hOld μc νc hcc hNextC hOldNe hOldParent
            ⟨hxOldA, hxOldB⟩
        have hxFine : x ∈ fineAllowed
            (EdgeTrainLevels.firstForgetIndex m R.extraCuts νc) :=
          hRetained νc hνTwo hOldVertex
        simpa only [hνEq] using hxFine

end StructuralRamsey.Girth
