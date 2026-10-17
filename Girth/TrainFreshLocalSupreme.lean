import Girth.TrainStrictPlanComplete
import Mathlib.Tactic

/-!
# Circulation: local fresh witnesses automatically assemble a supreme plan

If a chosen designated source label supplies, at every other occurrence,
a genuine short edge or a long pair with original vertex boundaries
and a wagon absent from the old connectors, choose all these witnesses
simultaneously. Retain EVERY occurrence of the chosen label.

The checked all-length strict PlanValid construction then gives a
legal acceptable BigCycle of exactly the same numerical order.
This reduces later arbitrary-replacement supreme composition to
producing local short/long witnesses at the ORIGINAL source positions,
rather than carrying a global second-cycle indexing system.

No appendix input, no output acceptability premise, and no new
combinatorial axiom.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Source-side local piece predicate, including precisely the freshness
needed to assemble all chosen long pieces into one literal cycle. -/
def BigCycle.FreshLocalPiece
    {n : ℕ} (C : D.BigCycle n) (k i : Fin n) :
    TrainSupremePiece E P → Prop
  | .keep => False
  | .short e => C.ShortValid D k i e
  | .long e p f =>
      C.LongValid D k i e p f ∧
        ∀ t : Fin n, C.connector t ≠ Sum.inr p

/-- Local fresh short/long witnesses give a complete simultaneous
supreme output with no extra global-plan assumption. -/
theorem BigCycle.hasSupremeAt_of_fresh_local_witnesses
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (k : Fin n) (hk : D.designated (C.label k))
    (hLocal : ∀ i : Fin n, C.label i ≠ C.label k →
      (∃ e : E, C.ShortValid D k i e) ∨
      (∃ (e f : E) (p : P),
        C.LongValid D k i e p f ∧
        ∀ t : Fin n, C.connector t ≠ Sum.inr p)) :
    C.HasSupremeAt D k := by
  classical
  have hWitness (i : Fin n) (hne : C.label i ≠ C.label k) :
      ∃ piece : TrainSupremePiece E P,
        C.FreshLocalPiece D k i piece := by
    rcases hLocal i hne with ⟨e, he⟩ | ⟨e, f, p, hv, hfresh⟩
    · exact ⟨.short e, he⟩
    · exact ⟨.long e p f, ⟨hv, hfresh⟩⟩
  let pieces : Fin n → TrainSupremePiece E P :=
    fun i => if h : C.label i = C.label k then .keep
      else Classical.choose (hWitness i h)
  have hSpec (i : Fin n) (hne : C.label i ≠ C.label k) :
      C.FreshLocalPiece D k i (pieces i) := by
    simpa [pieces, hne] using Classical.choose_spec (hWitness i hne)
  have hPlan : C.PlanValid D k pieces := by
    intro i
    constructor
    · intro hEq
      simp [pieces, hEq]
    · intro hNe
      have hv := hSpec i hNe
      cases hp : pieces i with
      | keep =>
          exact False.elim (by simpa [BigCycle.FreshLocalPiece, hp] using hv)
      | short e =>
          simpa [BigCycle.FreshLocalPiece, hp] using hv
      | long e p f =>
          have hLong : C.LongValid D k i e p f := by
            rw [hp] at hv
            exact hv.1
          simpa [hp] using hLong
  have hFresh :
      ∀ (i : Fin n) (e : E) (p : P) (f : E),
        pieces i = .long e p f →
        ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
    intro i e p f hPiece t
    by_cases hEq : C.label i = C.label k
    · have hKeep := (hPlan i).1 hEq
      rw [hPiece] at hKeep
      cases hKeep
    · have hv := hSpec i hEq
      rw [hPiece] at hv
      exact hv.2 t
  obtain ⟨m, B, _hAcc, _hOrder, hWord⟩ :=
    C.planProducesAcceptableOrder_all_lengths
      D hAccept hLinear k hk pieces hPlan hFresh
  exact ⟨hk, pieces, hPlan, m, B, hWord⟩

end StructuralRamsey.Girth.OrderOneData
