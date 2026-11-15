import Girth.TrainFillingPrivateTailWagonEquiv
import Girth.TrainFillingIndexedContractedTrainGirth

set_option Elab.async false

/-!
# Original tail girth -> actual heterogeneous shortened M girth

The original train T has height 1+m. Its true first-wagon
labels are the quotient of original physical edges at old
level one. The shortened target train on those labels
is T.tailQuotient: new level nu is old level nu+1.

The earlier checked indexed private-contraction theorem
can transfer labelled girth of this shortened target
to the heterogeneous private-extension M, choice by
choice. It was written with the old shortened
labelled cut-girth hypothesis for each EHN choice c.

There is no reason to assume that independently:
all c share the SAME original first-wagon carriers,
and the true tailQuotient has exactly the same
labelled wagon carriers and girth as the original
train at nu+1. We combine these equalities below.

Only the ACTUAL old labelled girth of T is a premise.
This theorem never assumes any girth of an output
Ramsey witness, filled H or selected designated copy.

Source candidate, not Lean-kernel checked.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {E V C X : Type v}

/-- Every actual selected choice has the same ORIGINAL
first-wagon vertex-carrier family, even though their
private X-coordinates and selected template edges differ. -/
theorem contractedChoiceTrain_labelledCutGirth_of_originalTail
    {m : ℕ}
    (T : EdgeTrainLevels E (m + 1))
    (edges : E → Set V)
    (U : C → PrivateWagonInput V T.FirstWagon X)
    (hm : 0 < m)
    (hCarriers : ∀ c : C, ∀ p : T.FirstWagon,
      (U c).oldCarrier p =
        T.wagonClassCarrier edges
          (EdgeTrainLevels.firstWagonLevel m) p)
    (μ : Fin (m + 1)) (hProper : μ.val < m)
    (g : ℕ)
    (hOriginal : LabelledGirthGT
      (T.wagonClassCarrier edges μ.succ) g) :
    LabelledGirthGT
      ((contractedChoiceTrain U T.tailQuotient hm).wagonClassCarrier
        (contractedCarrier U) μ) g := by
  have hOld : ∀ c : C,
      LabelledGirthGT
        (T.tailQuotient.wagonClassCarrier (U c).oldCarrier μ) g := by
    intro c
    have hCarrierEq :
        (U c).oldCarrier =
          T.wagonClassCarrier edges
            (EdgeTrainLevels.firstWagonLevel m) := by
      funext p
      exact hCarriers c p
    rw [hCarrierEq]
    exact (T.tailQuotient_labelledCutGirth_iff edges μ g).mpr
      hOriginal
  exact contractedChoiceTrain_labelledCutGirth
    U T.tailQuotient hm μ hProper g hOld

end StructuralRamsey.Girth.IndexedPrivateChoice
