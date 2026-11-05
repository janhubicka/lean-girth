import Girth.TrainRecursivePhysicalCutTransfer

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact retained positive labelled-cut girth of a true first-wagon refinement

A first-wagon refinement inserts extra cuts BELOW the original first
positive cut. It carries exact preservation and reflection of every
original positive train relation, not merely a projection of carriers.

The existing theorem that forgetting these cuts recovers the ORIGINAL
train identifies the entire retained quotient-labelled wagon family.
Thus a positive old labelled-cut girth bound transfers to its literal
retained fine coordinate, including the top cut. No new hypothesis on
the inserted cuts, on labels with coincident carriers, or on the
original first wagon being universal is required.

This is the RETAINED part of the positive target-cut inputs of the q>2
recursive lower call. The inserted lower positive cuts remain a
separate geometric obligation; this module does not assert that the
refinement itself has new global labelled girth.
-/

namespace StructuralRamsey.Girth

universe v

variable {E W P : Type v}
variable {m : ℕ} {T : EdgeTrainLevels E m}
variable {hm : 0 < m}
variable {edge : E → Set W} {part : W → P}
variable {firstAllowed : Set P} {g : ℕ}

/-- At each POSITIVE old coordinate, the genuine refined train has
the exact same quotient-labelled horizontal cut as the old train,
at the shifted fine index. This direction is intentionally the
reverse of the already checked forgetful transport. -/
theorem FirstWagonRefinement.labelledGirthGT_at_retained
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (μ : Fin (m + 1)) (hμ : 0 < μ.val)
    (q : ℕ)
    (hOld : LabelledGirthGT
      (T.wagonClassCarrier edge μ) q) :
    LabelledGirthGT
      (R.train.wagonClassCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ)) q := by
  have hForget : R.train.forgetFirstCuts hm = T :=
    R.forget_train_eq
  rw [← hForget] at hOld
  change LabelledGirthGT
    (R.train.wagonClassCarrier edge
      (EdgeTrainLevels.firstForgetIndex m R.extraCuts μ)) q at hOld
  have hIndex :
      EdgeTrainLevels.firstForgetIndex m R.extraCuts μ =
        EdgeTrainLevels.firstRefinementShift m R.extraCuts μ :=
    EdgeTrainLevels.firstForgetIndex_of_pos m R.extraCuts μ hμ
  rw [hIndex] at hOld
  exact hOld

/-- Any lower requested cutoff at a retained positive coordinate is
also available, preserving all physical edge and wagon labels. -/
theorem FirstWagonRefinement.labelledGirthGT_at_retained_mono
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (μ : Fin (m + 1)) (hμ : 0 < μ.val)
    (q q' : ℕ) (hLower : q' ≤ q)
    (hOld : LabelledGirthGT
      (T.wagonClassCarrier edge μ) q) :
    LabelledGirthGT
      (R.train.wagonClassCarrier edge
        (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ)) q' :=
  labelledGirthGT_mono
    (R.labelledGirthGT_at_retained μ hμ q hOld) hLower

end StructuralRamsey.Girth
