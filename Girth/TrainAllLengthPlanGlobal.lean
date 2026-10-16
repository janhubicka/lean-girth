import Girth.TrainTwoOccurrenceMixedLong
import Girth.TrainPlanCyclicWrap
import Mathlib.Tactic

/-!
# Circulation: literal simultaneous supreme-plan legality at every length

The already checked source-length>=3 theorem constructs the ACTUAL
flattened short/long replacement BigCycle using fresh inserted wagons.
The two-occurrence theorem checks the only remaining case directly,
including one long piece and a retained designated occurrence.

Combining them eliminates the artificial case split from subsequent
circulation applications. No output-wagon linearity or preconstructed
output cycle is assumed; nor are output A2/A3 acceptability, numerical
order or composition of successive supreme collapses claimed here.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every locally valid strict supreme plan with genuinely fresh long
wagons produces its literal BigCycle word, at EVERY source length.
For length two the sole non-kept occurrence is short or one long piece;
for length at least three the checked cyclic-word assembly applies. -/
theorem BigCycle.planProducesBigCycle_of_fresh_long_all_lengths
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.PlanProducesBigCycle D pieces := by
  by_cases hTwo : n = 2
  · subst n
    exact C.planProducesBigCycle_two_of_fresh_long D k hk pieces hPlan
  · have hThree : 3 ≤ n := by
      have hMin : 2 ≤ n := C.length_ge_two
      omega
    exact C.planProducesBigCycle_of_fresh_long D
      hAccept hThree k hk pieces hPlan hFresh

/-- Construct the actual indexed simultaneous supreme copy directly
from short/long PlanValid data and fresh wagons at every source length.
The designated target must be an existing source occurrence. -/
theorem BigCycle.hasSupremeAt_of_planValid_fresh
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.HasSupremeAt D k :=
  ⟨hk, pieces, hPlan,
    C.planProducesBigCycle_of_fresh_long_all_lengths D
      hAccept k hk pieces hPlan hFresh⟩

/-- The unindexed form used directly by FullSystemGirthGT. This
closes global BIGCYCLE LEGALITY for selected fresh strict plans only,
not the acceptability of that result or broad arbitrary replacements. -/
theorem BigCycle.hasSimultaneousSupreme_of_planValid_fresh
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.HasSimultaneousSupreme :=
  C.hasSimultaneousSupreme_of_hasSupremeAt D k
    (C.hasSupremeAt_of_planValid_fresh D hAccept k hk pieces
      hPlan hFresh)

end StructuralRamsey.Girth.OrderOneData
