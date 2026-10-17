import Girth.TrainLiteralMixedOrder
import Girth.TrainTwoOccurrencePlanGlobal

/-!
# Circulation: strict simultaneous replacement preserves acceptability and order

The checked global literal-word construction and A1--A3 transfer work
at every source length, including the two-occurrence one-long case.
The separate numeric-order theorem now identifies the order of that
ACTUAL output word with the source order.

This assembles the complete strict PlanValid simultaneous-replacement
statement used by the circulation proof: there is a genuine acceptable
output cycle of the same twice-order.

This deliberately does NOT assert the broader manuscript claim about
arbitrary replacements and composition of supreme copies. Those still
need an independent validation. No appendix theorem is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An acceptable fresh strict PlanValid simultaneous replacement
preserves the exact numerical order and remains acceptable, at EVERY
source length. -/
theorem BigCycle.planProducesAcceptableOrder_all_lengths
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧ B.twiceOrder = C.twiceOrder ∧
      List.ofFn (fun i : Fin m => (B.label i, B.connector i)) =
        C.resultWord D pieces := by
  obtain ⟨m, B, hOutputAccept, hWord⟩ :=
    C.planProducesAcceptable_all_lengths
      D hAccept hLinear k hk pieces hPlan hFresh
  exact ⟨m, B, hOutputAccept,
    C.literal_resultWord_twiceOrder D B k pieces hPlan hWord, hWord⟩

end StructuralRamsey.Girth.OrderOneData
