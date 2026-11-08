import Girth.TrainStrictPlanComplete
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a true original length-two LONG is globally supreme

A genuine acceptable BigCycle of source length TWO has a designated
target at one original index. Suppose it has a true LongValid
replacement for the OTHER original index, with two physical A-edges
e,f in a common wagon w and the genuine non-PairEdge requirement.

The two original connectors are necessarily vertices (by the
LongValid boundary conditions), so w is FRESH against every
original connector. The literal one-keep/one-long chosen plan is
therefore PlanValid and satisfies strict wagon freshness. The
already checked all-length strict-plan theorem constructs the
globally legal expanded three-occurrence BigCycle, preserving
acceptability and numerical twice-order. Hence the original
length-two cycle has a genuine indexed HasSupremeAt.

This isolates the last source-length-two long case: the remaining
mathematical task is proving the existence of a genuine LongValid
owned by the ORIGINAL designated B-copy (not merely its reduced
geometric standard) from old/witness girth and strongness.
No appendix or manuscript changes.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- For any acceptable linear genuine length-two BigCycle, a
designated ORIGINAL target with LongValid at its opposite occurrence
already has a globally valid simultaneous supreme replacement plan. -/
theorem BigCycle.two_hasSupremeAt_of_longValid
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (target : Fin 2)
    (hTarget : D.designated (Z.label target))
    (e f : E) (w : P)
    (hLong : Z.LongValid D target (cyclicSucc target) e w f) :
    Z.HasSupremeAt D target := by
  classical
  let other : Fin 2 := cyclicSucc target
  let pieces : Fin 2 → TrainSupremePiece E P :=
    fun j => if j = target then .keep else .long e w f
  have hPlan : Z.PlanValid D target pieces := by
    intro j
    by_cases hj : j = target
    · subst j
      constructor
      · intro _
        simp [pieces]
      · intro hDiff
        exact False.elim (hDiff rfl)
    · have hOther : j = other := by
        fin_cases target <;> fin_cases j <;>
          simp_all [other, cyclicSucc]
      have hDifferent : Z.label j ≠ Z.label target := by
        rw [hOther]
        exact (Z.adjacent_ne target).symm
      constructor
      · intro hSame
        exact False.elim (hDifferent hSame)
      · intro _
        have hp : pieces j = .long e w f := by
          simp [pieces, hj]
        have hJ : Z.LongValid D target j e w f := by
          simpa only [hOther] using hLong
        simpa only [hp] using hJ
  obtain ⟨x, y, hPrev, hHere, _he, _hf, _hne,
    _hpe, _hpf, _hxe, _hyf, _hNoPair⟩ := hLong
  have hPredOther : trainCyclicPred other = target := by
    dsimp [other]
    exact trainCyclicPred_cyclicSucc_of_two_le (by decide : 2 ≤ 2) target
  have hTargetConnector : Z.connector target = Sum.inl x := by
    rw [hPredOther] at hPrev
    exact hPrev
  have hOtherConnector : Z.connector other = Sum.inl y := hHere
  have hWagonFresh : ∀ t : Fin 2,
      Z.connector t ≠ Sum.inr w := by
    intro t ht
    by_cases hEq : t = target
    · rw [hEq, hTargetConnector] at ht
      cases ht
    · have hTo : t = other := by
        fin_cases target <;> fin_cases t <;>
          simp_all [other, cyclicSucc]
      rw [hTo, hOtherConnector] at ht
      cases ht
  have hFresh : ∀ (j : Fin 2) (a : E) (p : P) (b : E),
      pieces j = .long a p b →
      ∀ t : Fin 2, Z.connector t ≠ Sum.inr p := by
    intro j a p b hp t
    by_cases hj : j = target
    · simp [pieces, hj] at hp
    · have hPiece :
          (TrainSupremePiece.long e w f : TrainSupremePiece E P) =
            TrainSupremePiece.long a p b := by
        simpa [pieces, hj] using hp
      have hP : p = w := by
        injection hPiece with _ hW _
        exact hW.symm
      rw [hP]
      exact hWagonFresh t
  obtain ⟨m, H, _hAcceptH, _hSameOrder, hWord⟩ :=
    Z.planProducesAcceptableOrder_all_lengths
      D hAccept hLinear target hTarget pieces hPlan hFresh
  exact ⟨hTarget, pieces, hPlan, ⟨m, H, hWord⟩⟩

end StructuralRamsey.Girth.OrderOneData
