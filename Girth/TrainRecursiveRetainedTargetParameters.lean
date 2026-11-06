import Girth.TrainRecursiveCanonicalFineAllowed
import Girth.TrainRecursiveRefinementForget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine retained positive fine-train parameters from the OLD target train

In a FirstWagonRefinement, the old positive train levels are reflected
EXACTLY by the fine levels shifted by extraCuts. The last inserted
parent (fine cut extraCuts+1) has its own R.parameters certificate.
Every later adjacent fine parent is the shift of a genuine adjacent
OLD positive parent.

We transfer its complete TrainParentIntersectionBound without
pruning edge labels or quotienting wagon labels by their physical
carrier. The transport goes via actual representatives of the two
quotient-labelled child wagons and R.oldLevels at both cuts.

Finally, at old positive parent indices >=2, the canonical
fineAllowedFromRefinement is exactly the pullback of the old allowed
P-parts. If oldPart = alpha ∘ activePart on the true active vertex
set, the retained old parameter bound becomes the A-partite fine
target parameter bound required for the recursive lower stage.

This is conditional on the OLD active physical train's genuine
AdjacentParameters certificate. Establishing that certificate
through the exact active-edge restriction is a separate geometry
step. The first retained GLOBAL labelled girth and output
SupremeCycleBound are not inferred. No appendix.
-/

namespace StructuralRamsey.Girth

open TrainRecursiveWitness

universe v
variable {E W UA P : Type v}
variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {oldPart : W → P}
variable {firstAllowed : Set P} {g : ℕ}

/-- For any adjacent OLD positive cuts μ<ν with μ>=1, the true
shifted fine cut inherits exactly the old sibling-intersection
bound, using the real physical edge and quotient wagon carriers. -/
theorem FirstWagonRefinement.retained_adjacentParameter_of_old
    (R : FirstWagonRefinement T hm edge oldPart firstAllowed g)
    (oldAllowed : Fin (m + 1) → Set P)
    (hOld : T.AdjacentParameters edge
      (fun ν => oldPart ⁻¹' oldAllowed ν))
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hSucc : ν.val = μ.val + 1) (hμpos : 0 < μ.val) :
    TrainParentIntersectionBound
      (R.train.wagonClassCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ))
      (R.train.wagonParent
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ)
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν)
        (by
          change μ.val + R.extraCuts ≤ ν.val + R.extraCuts
          omega))
      (oldPart ⁻¹' oldAllowed ν) := by
  have hνpos : 0 < ν.val := by omega
  intro a b hne hParent x hx
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      have hOldNe :
          (Quotient.mk (T.wagonSetoid μ) a :
            Quotient (T.wagonSetoid μ)) ≠
          Quotient.mk (T.wagonSetoid μ) b := by
        intro heq
        apply hne
        exact Quotient.sound
          ((R.oldLevels μ hμpos a b).mpr (Quotient.exact heq))
      have hFineParent : R.train.rel
          (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν) a b := by
        apply Quotient.exact
        change
          (Quotient.mk
            (R.train.wagonSetoid
              (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν)) a) =
          Quotient.mk
            (R.train.wagonSetoid
              (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν)) b
          at hParent
        exact hParent
      have hOldParent :
          T.wagonParent μ ν hμν
            (Quotient.mk (T.wagonSetoid μ) a) =
          T.wagonParent μ ν hμν
            (Quotient.mk (T.wagonSetoid μ) b) :=
        Quotient.sound ((R.oldLevels ν hνpos a b).mp hFineParent)
      obtain ⟨hxA, hxB⟩ := hx
      change x ∈ R.train.wagonCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ) a at hxA
      change x ∈ R.train.wagonCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ) b at hxB
      obtain ⟨c, hac, hxc⟩ := hxA
      obtain ⟨d, hbd, hxd⟩ := hxB
      have hxOldA : x ∈ T.wagonCarrier edge μ a :=
        ⟨c, (R.oldLevels μ hμpos a c).mp hac, hxc⟩
      have hxOldB : x ∈ T.wagonCarrier edge μ b :=
        ⟨d, (R.oldLevels μ hμpos b d).mp hbd, hxd⟩
      exact hOld μ ν hμν hSucc
        (Quotient.mk (T.wagonSetoid μ) a)
        (Quotient.mk (T.wagonSetoid μ) b)
        hOldNe hOldParent x ⟨hxOldA, hxOldB⟩

/-- The same retained bound in the TRUE ACTIVE A-partite coordinates.
At old parent ν>=2, its fine shifted coordinate uses exactly the
original allowed P-parts pulled back along alpha and activePart. -/
theorem FirstWagonRefinement.canonicalRetained_adjacentParameter
    (R : FirstWagonRefinement T hm edge oldPart firstAllowed g)
    (α : UA ↪ P) (activePart : W → UA)
    (hPart : ∀ x : W, oldPart x = α (activePart x))
    (oldAllowed : Fin (m + 1) → Set P)
    (hOld : T.AdjacentParameters edge
      (fun ν => oldPart ⁻¹' oldAllowed ν))
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hSucc : ν.val = μ.val + 1) (hμpos : 0 < μ.val) :
    TrainParentIntersectionBound
      (R.train.wagonClassCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ))
      (R.train.wagonParent
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ)
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν)
        (by
          change μ.val + R.extraCuts ≤ ν.val + R.extraCuts
          omega))
      (activePart ⁻¹'
        (fineAllowedFromRefinement m R.extraCuts hm
          α oldAllowed R.permitted
          (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν))) := by
  have hνpos : 0 < ν.val := by omega
  have hνgt : 1 < ν.val := by omega
  have hAllowedEq :
      activePart ⁻¹'
        (fineAllowedFromRefinement m R.extraCuts hm
          α oldAllowed R.permitted
          (EdgeTrainLevels.firstRefinementShift m R.extraCuts ν)) =
      oldPart ⁻¹' oldAllowed ν := by
    rw [← EdgeTrainLevels.firstForgetIndex_of_pos
      m R.extraCuts ν hνpos]
    rw [fineAllowedFromRefinement_retained_gt_one
      m R.extraCuts hm α oldAllowed R.permitted ν hνgt]
    ext x
    change α (activePart x) ∈ oldAllowed ν ↔
      oldPart x ∈ oldAllowed ν
    rw [hPart x]
  rw [hAllowedEq]
  exact R.retained_adjacentParameter_of_old
    oldAllowed hOld μ ν hμν hSucc hμpos

end StructuralRamsey.Girth
