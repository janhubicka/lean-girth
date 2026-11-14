import Girth.TrainBottomForestReducedNoA1
import Girth.TrainShortOnlyPlanGlobal

/-!
# Every genuine bottom supreme plan is automatically short-only

At equality on physical edge labels, one wagon contains only one
edge. A LongValid piece would require two distinct edges with the
same wagon parent, which is impossible by bottom parent injectivity.

The reduction's global simultaneous supreme plan therefore has
only keep/short replacements. No long-piece source geometry, fresh
wagon choice or designated-label quotient is needed in the bottom
branch. The actual original B-labelled transfer remains separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Distinct genuine physical edges cannot form one bottom long piece. -/
theorem BottomForestGeometry.no_long_valid
    (H : D.BottomForestGeometry)
    {n : ℕ} (C : D.BigCycle n)
    (target j : Fin n) (e : E) (w : P) (f : E)
    (hLong : C.LongValid D target j e w f) : False := by
  obtain ⟨x, y, hLeft, hRight, heOwned, hfOwned,
    hDiff, heParent, hfParent, hx, hy, hNonedge⟩ := hLong
  exact hDiff (H.parent_injective (heParent.trans hfParent.symm))

/-- Any valid global simultaneous bottom supreme plan contains NO
long pieces. This is a consequence of its original PlanValid record,
not a replacement of global supremeness by local pieces. -/
theorem BigCycle.bottom_plan_short_only
    (H : D.BottomForestGeometry)
    {n : ℕ} (C : D.BigCycle n)
    (target : Fin n) (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D target pieces) :
    ∀ j : Fin n, (pieces j).IsShortOrKeep := by
  intro j
  cases hj : pieces j with
  | keep => trivial
  | short e => trivial
  | long e w f =>
      have hDifferent : C.label j ≠ C.label target := by
        intro hEq
        have hk := (hPlan j).1 hEq
        rw [hj] at hk
        cases hk
      have hLong : C.LongValid D target j e w f := by
        simpa only [hj] using (hPlan j).2 hDifferent
      exact False.elim (H.no_long_valid D C target j e w f hLong)

/-- The complete existing bottom supremeness theorem can be
unpacked with a short-only physical plan. Every source occurrence
and its original designated index remain literally present. -/
theorem BigCycle.has_short_only_supreme_of_bottom_global
    (H : D.BottomForestGeometry)
    {n : ℕ} (C : D.BigCycle n)
    (hSupreme : C.HasSimultaneousSupreme) :
    ∃ target : Fin n,
      D.designated (C.label target) ∧
      ∃ pieces : Fin n → TrainSupremePiece E P,
        C.PlanValid D target pieces ∧
        C.PlanProducesBigCycle D pieces ∧
        (∀ j : Fin n, (pieces j).IsShortOrKeep) := by
  obtain ⟨target, hDesignated, pieces, hPlan, hGlobal⟩ := hSupreme
  exact ⟨target, hDesignated, pieces, hPlan, hGlobal,
    C.bottom_plan_short_only D H target pieces hPlan⟩

end StructuralRamsey.Girth.OrderOneData
