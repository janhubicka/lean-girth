import Girth.TrainPlanCyclicWrap
import Girth.TrainOutputA1Length
import Girth.TrainLiteralOutputA2
import Girth.TrainLiteralOldPosA3

/-!
# Circulation: strict supreme replacement preserves acceptability

Combines independently checked components of a fresh strict PlanValid
simultaneous replacement: literal output BigCycle construction, automatic
A1 at source length at least three, physical wagon-contact A2 transfer,
and inserted-wagon no-splitting A3 transfer from source linearity.

Only this strict indexed simultaneous-plan case is asserted. Arbitrary
replacement-plan composition, preservation of supreme labels outside a
strict plan, the length-two separate case, and the girth theorem remain
separate open obligations. No appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Actual acceptable output cycle for any fresh strict PlanValid
simultaneous supreme plan at source length at least three. -/
theorem BigCycle.planProducesAcceptable_of_fresh_long
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧
      List.ofFn (fun i : Fin m => (B.label i, B.connector i)) =
        C.resultWord D pieces := by
  obtain ⟨m, B, hWord⟩ :=
    C.planProducesBigCycle_of_fresh_long
      D hAccept hn k hk pieces hPlan hFresh
  refine ⟨m, B, ?_, hWord⟩
  exact ⟨C.output_A1_of_source_length_three D B hn pieces hWord,
    C.output_A2_of_literal_resultWord D B
      hAccept hn k pieces hPlan hFresh hWord,
    C.output_A3_of_literal_resultWord D B
      hAccept hLinear k pieces hPlan hFresh hWord⟩

end StructuralRamsey.Girth.OrderOneData
