import Girth.TrainTwoStageLongComposition
import Girth.TrainShortOnlyPlanGlobal

/-!
# Circulation: later supreme pieces at wagon boundaries are short

A long supreme replacement is legal only between TWO original vertex
connectors. If either boundary is a wagon connector, a non-target
occurrence can only be replaced by a short actual edge.

Applied to the two edge occurrences of a first long block e+ W f+,
these facts supply precisely the two later shorts needed by the
checked two-bridge recombination lemma. They use no output cycle
acceptability, linearity or appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A non-target occurrence whose RIGHT connector is a wagon can
only receive a later short piece in a PlanValid supreme replacement. -/
theorem BigCycle.short_piece_of_wagon_right
    {m : ℕ} (B : D.BigCycle m)
    (k j : Fin m)
    (pieces : Fin m → TrainSupremePiece E P)
    (hPlan : B.PlanValid D k pieces)
    (hNotTarget : B.label j ≠ B.label k)
    (p : P) (hWagon : B.connector j = Sum.inr p) :
    ∃ e : E, pieces j = .short e ∧ B.ShortValid D k j e := by
  cases hp : pieces j with
  | keep =>
      have hf := (hPlan j).2 hNotTarget
      rw [hp] at hf
      exact False.elim hf
  | short e =>
      exact ⟨e, hp,
        B.shortValid_of_piece_eq_short D k j pieces hPlan e hp⟩
  | long e q f =>
      have hv := B.longValid_of_piece_eq_long
        D k j pieces hPlan e f q hp
      obtain ⟨x, y, _hBefore, hHere, _he, _hf, _hne,
        _hPe, _hPf, _hXe, _hYf, _hNonedge⟩ := hv
      have hBad : (Sum.inr p : V ⊕ P) = Sum.inl y :=
        hWagon.symm.trans hHere
      cases hBad

/-- Likewise, a non-target occurrence with a wagon immediately
to its LEFT cannot receive a long replacement. -/
theorem BigCycle.short_piece_of_wagon_left
    {m : ℕ} (B : D.BigCycle m)
    (k j : Fin m)
    (pieces : Fin m → TrainSupremePiece E P)
    (hPlan : B.PlanValid D k pieces)
    (hNotTarget : B.label j ≠ B.label k)
    (p : P)
    (hWagon : B.connector (trainCyclicPred j) = Sum.inr p) :
    ∃ e : E, pieces j = .short e ∧ B.ShortValid D k j e := by
  cases hp : pieces j with
  | keep =>
      have hf := (hPlan j).2 hNotTarget
      rw [hp] at hf
      exact False.elim hf
  | short e =>
      exact ⟨e, hp,
        B.shortValid_of_piece_eq_short D k j pieces hPlan e hp⟩
  | long e q f =>
      have hv := B.longValid_of_piece_eq_long
        D k j pieces hPlan e f q hp
      obtain ⟨x, y, hBefore, _hHere, _he, _hf, _hne,
        _hPe, _hPf, _hXe, _hYf, _hNonedge⟩ := hv
      have hBad : (Sum.inr p : V ⊕ P) = Sum.inl x :=
        hWagon.symm.trans hBefore
      cases hBad

end StructuralRamsey.Girth.OrderOneData
