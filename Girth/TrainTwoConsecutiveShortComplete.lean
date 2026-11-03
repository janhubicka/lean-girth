import Girth.TrainArbitraryReplacementComplete
import Mathlib.Tactic

/-!
# Path A: two consecutive physical short pieces need no new wagon

The missing replacement for an old-wagon long piece is not another
long insertion. Two consecutive source occurrences already use the
same middle connector. Replacing those two labels by physical edges
incident with the original left/middle and middle/right connectors
produces an actual acceptable BigCycle of the same numerical order.

The fully checked arbitrary-replacement theorem gives output legality,
A1--A3, and supreme pullback, with no common designated source target
and NO fresh-wagon requirement. A rank reduction is NOT claimed here.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Replace the labels of two CONSECUTIVE occurrences by physical
short edges; the old connector word is left unchanged. -/
def BigCycle.twoConsecutiveShortPieces
    {n : ℕ} (C : D.BigCycle n) (t : Fin n)
    (first second : E) : Fin n → TrainSupremePiece E P :=
  fun j => if j = t then .short first
    else if j = cyclicSucc t then .short second
    else .keep

/-- Two genuine adjacent physical short edges suffice for an actual
globally legal acceptable replacement. No inserted wagon, no source
label membership assumptions, and no selected supreme target.
All later supreme labels pull back to the original source cycle. -/
theorem BigCycle.twoConsecutiveShort_complete_of_three_le
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (t : Fin n) (first second : E)
    (hFirst : D.Incident (.inr first)
        (C.connector (trainCyclicPred t)) ∧
      D.Incident (.inr first) (C.connector t))
    (hSecond : D.Incident (.inr second) (C.connector t) ∧
      D.Incident (.inr second) (C.connector (cyclicSucc t))) :
    ∃ m : ℕ, ∃ H : D.BigCycle m,
      List.ofFn (fun j : Fin m =>
        (H.label j, H.connector j)) =
        C.resultWord D (C.twoConsecutiveShortPieces D t first second) ∧
      H.Acceptable ∧ H.twiceOrder = C.twiceOrder ∧
      (∀ kH : Fin m, H.HasSupremeAt D kH →
        ∃ kC : Fin n, C.label kC = H.label kH ∧
          C.HasSupremeAt D kC) := by
  let pieces := C.twoConsecutiveShortPieces D t first second
  have hNe : cyclicSucc t ≠ t :=
    cyclicSucc_ne_self_of_two_le (by omega : 2 ≤ n) t
  have hInc : C.LocalPieceIncidence D pieces := by
    intro j
    by_cases hJt : j = t
    · subst j
      simpa [pieces, BigCycle.twoConsecutiveShortPieces,
        BigCycle.LocalPieceIncidence] using hFirst
    · by_cases hJs : j = cyclicSucc t
      · subst j
        have hPred : trainCyclicPred (cyclicSucc t) = t :=
          trainCyclicPred_cyclicSucc_of_two_le (by omega : 2 ≤ n) t
        simpa [pieces, BigCycle.twoConsecutiveShortPieces,
          BigCycle.LocalPieceIncidence, hNe, hPred] using hSecond
      · simp [pieces, BigCycle.twoConsecutiveShortPieces,
          BigCycle.LocalPieceIncidence, hJt, hJs]
  have hNoLong :
      ∀ (j : Fin n) (e f : E) (p : P),
        pieces j ≠ TrainSupremePiece.long e p f := by
    intro j e f p
    by_cases hJt : j = t
    · simp [pieces, BigCycle.twoConsecutiveShortPieces, hJt]
    · by_cases hJs : j = cyclicSucc t
      · simp [pieces, BigCycle.twoConsecutiveShortPieces, hJt, hJs]
      · simp [pieces, BigCycle.twoConsecutiveShortPieces, hJt, hJs]
  have hGeom : C.LocalLongA2Geometry D pieces := by
    intro j e f p hp
    exact False.elim ((hNoLong j e f p) hp)
  have hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ s : Fin n, C.connector s ≠ Sum.inr p := by
    intro j e p f hp
    exact False.elim ((hNoLong j e f p) hp)
  exact C.arbitrary_replacement_complete_of_three_le
    D hAccept hLinear hn pieces hInc hGeom hFresh

end StructuralRamsey.Girth.OrderOneData
