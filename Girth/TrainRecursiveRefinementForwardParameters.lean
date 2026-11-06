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
  intro μ ν hμν hNext
  by_cases hInsertedLevel : ν.val ≤ R.extraCuts + 1
  · let j : Fin (R.extraCuts + 1) := ⟨μ.val, by omega⟩
    have hμ :
        μ = firstRefinementChild m R.extraCuts hm j := by
      apply Fin.ext
      rfl
    have hν :
        ν = firstRefinementParent m R.extraCuts hm j := by
      apply Fin.ext
      change ν.val = μ.val + 1
      exact hNext
    have hFineChild : TrainParentIntersectionBound
        (R.train.wagonClassCarrier edge
          (firstRefinementChild m R.extraCuts hm j))
        (R.train.wagonParent
          (firstRefinementChild m R.extraCuts hm j)
          (firstRefinementParent m R.extraCuts hm j)
          (by change j.val ≤ j.val + 1; omega))
        (fineAllowed (firstRefinementParent m R.extraCuts hm j)) := by
      intro a b hab hp x hx
      exact hInserted j (R.parameters j hab hp hx)
    cases hμ
    cases hν
    exact hFineChild
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
      change ν.val - R.extraCuts = μ.val - R.extraCuts + 1
      omega
    have hμEq :
        EdgeTrainLevels.firstForgetIndex m R.extraCuts μc = μ := by
      apply Fin.ext
      change (if μc.val = 0 then 0 else μc.val + R.extraCuts) = μ.val
      simp only [Nat.ne_of_gt hμPos, ↓reduceIte]
      change μ.val - R.extraCuts + R.extraCuts = μ.val
      omega
    have hνEq :
        EdgeTrainLevels.firstForgetIndex m R.extraCuts νc = ν := by
      apply Fin.ext
      change (if νc.val = 0 then 0 else νc.val + R.extraCuts) = ν.val
      simp only [Nat.ne_of_gt hνPos, ↓reduceIte]
      change ν.val - R.extraCuts + R.extraCuts = ν.val
      omega
    have hForget :
        (R.train.forgetFirstCuts hm).AdjacentParameters edge oldAllowed := by
      rw [R.forget_train_eq]
      exact hOld
    have hBound :=
      R.train.retainedParentBound_of_forgotten hm edge μc νc hcc
        (oldAllowed νc) (fineAllowed ν)
        (by simpa [hνEq] using hRetained νc hνTwo)
        (hForget μc νc hcc hNextC)
    cases hμEq
    cases hνEq
    exact hBound

end StructuralRamsey.Girth
