import Girth.TrainTwoCycleOriginalShortSupreme
import Girth.TrainTwoCycleOriginalLongSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: at original length TWO, any owned short/long local piece
is automatically a GLOBAL supreme replacement

A genuine acceptable linear source BigCycle of length two has an
ORIGINAL designated target. If its original target supplies the
manuscript's true local ShortPiece or LongPiece through both original
source connectors, then the already checked one-short or one-long
strict all-length constructors produce a globally valid HasSupremeAt
at THAT EXACT original source label, preserving actual physical
support edges and wagon classes.

This reduces the remaining n=2 output-girth obligation to real
local-piece EXISTENCE in the ORIGINAL selected B-copy. A piece
belonging merely to the geometric reduced witness standard does not
suffice, and no such false identification is made here.
No appendix or manuscript changes.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In the original actual source BigCycle of length two, any
genuine ShortPiece or LongPiece of the designated original target
automatically extends to a globally legal HasSupremeAt. -/
theorem BigCycle.two_hasSupremeAt_of_original_local_piece
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (target : Fin 2)
    (hTarget : D.designated (Z.label target))
    (hPiece :
      D.ShortPiece (Z.label target)
        (Z.connector (trainCyclicPred (cyclicSucc target)))
        (Z.connector (cyclicSucc target)) ∨
      D.LongPiece (Z.label target)
        (Z.connector (trainCyclicPred (cyclicSucc target)))
        (Z.connector (cyclicSucc target))) :
    Z.HasSupremeAt D target := by
  have hPred : trainCyclicPred (cyclicSucc target) = target :=
    trainCyclicPred_cyclicSucc_of_two_le (by decide : 2 ≤ 2) target
  rcases hPiece with hShort | hLong
  · obtain ⟨e, hOwned, hLeft, hRight⟩ := hShort
    have hLeftTarget : D.Incident (.inr e) (Z.connector target) := by
      simpa only [hPred] using hLeft
    have hBoth : ∀ j : Fin 2,
        D.Incident (.inr e) (Z.connector j) := by
      intro j
      by_cases hj : j = target
      · rw [hj]
        exact hLeftTarget
      · have hOther : j = cyclicSucc target := by
          fin_cases target <;> fin_cases j <;>
            simp_all [cyclicSucc]
        rw [hOther]
        exact hRight
    exact BigCycle.two_hasSupremeAt_of_common_short
      D Z hAccept hLinear target hTarget e hOwned hBoth
  · obtain ⟨x, y, w, e, f, hLeft, hRight, hE, hF,
      hDistinct, hParentE, hParentF, hXe, hYf, hNoPair⟩ := hLong
    have hValid :
        Z.LongValid D target (cyclicSucc target) e w f :=
      ⟨x, y, hLeft, hRight, hE, hF,
        hDistinct, hParentE, hParentF, hXe, hYf, hNoPair⟩
    exact BigCycle.two_hasSupremeAt_of_longValid
      D Z hAccept hLinear target hTarget e f w hValid

end StructuralRamsey.Girth.OrderOneData
