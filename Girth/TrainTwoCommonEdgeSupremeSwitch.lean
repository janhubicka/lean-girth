import Girth.TrainStrictPlanComplete
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: an actual common short edge permits changing a two-cycle target

For a genuine two-occurrence BigCycle, if an edge of a designated
target is incident with BOTH real source connectors, the literal
one-short / one-keep plan is globally valid. Existing all-length
strict-plan completion supplies the resulting genuine BigCycle;
there is no merely local-piece surrogate.

If BOTH labels are designated and a SAME physical edge belongs
to BOTH prescribed edge families, and meets BOTH connectors, EITHER
actual designated occurrence can be chosen as a supreme target.
This is the precise plan-switching interface for the pair-edge
two-standard case, conditional on deriving the shared edge from
physical A-strongness and the actual owner-carrier geometry.

No unsupported claim of a common edge, no original-source expansion,
no long branch, no appendix and no manuscript text modification.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Build a GLOBAL one-short supreme plan at a specified designated
target from an actual edge meeting both length-two connectors.
The output BigCycle is produced by the checked strict-plan theorem. -/
theorem BigCycle.two_hasSupremeAt_of_common_short
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (target : Fin 2)
    (hTarget : D.designated (Z.label target))
    (e : E)
    (hOwned : e ∈ D.edges (Z.label target))
    (hBoth : ∀ j : Fin 2, D.Incident (.inr e) (Z.connector j)) :
    Z.HasSupremeAt D target := by
  classical
  let pieces : Fin 2 → TrainSupremePiece E P :=
    fun j => if j = target then .keep else .short e
  have hPlan : Z.PlanValid D target pieces := by
    intro j
    by_cases hj : j = target
    · subst j
      constructor
      · intro _
        simp [pieces]
      · intro hDiff
        exact False.elim (hDiff rfl)
    · have hOther : j = cyclicSucc target := by
        fin_cases target <;> fin_cases j <;>
          simp_all [cyclicSucc]
      have hDifferent : Z.label j ≠ Z.label target := by
        rw [hOther]
        exact (Z.adjacent_ne target).symm
      constructor
      · intro hSame
        exact False.elim (hDifferent hSame)
      · intro _
        have hp : pieces j = .short e := by simp [pieces, hj]
        have hShort : Z.ShortValid D target j e :=
          ⟨hOwned, hBoth (trainCyclicPred j), hBoth j⟩
        simpa only [hp] using hShort
  have hFresh : ∀ (j : Fin 2) (a : E) (w : P) (b : E),
      pieces j = .long a w b →
      ∀ t : Fin 2, Z.connector t ≠ Sum.inr w := by
    intro j a w b hLong t
    by_cases hj : j = target
    · simp [pieces, hj] at hLong
    · simp [pieces, hj] at hLong
  obtain ⟨m, H, _hAcceptH, _hSameOrder, hWord⟩ :=
    Z.planProducesAcceptableOrder_all_lengths D
      hAccept hLinear target hTarget pieces hPlan hFresh
  exact ⟨hTarget, pieces, hPlan, ⟨m, H, hWord⟩⟩

/-- Both designated reduced labels can be made actual supreme targets
using ONE common edge. This does not assert that the common edge
exists from arbitrary pair-edge or carrier-containment data alone. -/
theorem BigCycle.two_both_designated_supreme_of_common_short
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain)
    (hDesignated : ∀ target : Fin 2,
      D.designated (Z.label target))
    (e : E)
    (hOwned : ∀ target : Fin 2, e ∈ D.edges (Z.label target))
    (hBoth : ∀ j : Fin 2, D.Incident (.inr e) (Z.connector j)) :
    ∀ target : Fin 2, Z.HasSupremeAt D target := by
  intro target
  exact BigCycle.two_hasSupremeAt_of_common_short D Z
    hAccept hLinear target (hDesignated target)
    e (hOwned target) hBoth

end StructuralRamsey.Girth.OrderOneData
