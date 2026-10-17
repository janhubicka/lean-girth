import Girth.TrainStrictPlanAcceptability
import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

/-!
# Circulation: strict replacement at order one

An order-one big cycle has exactly two occurrences with mixed connector
kinds. Hence no source occurrence has two vertex boundaries, so a legal
long replacement is impossible. Every strict PlanValid plan is short-only.

The checked short-only BigCycle construction then has exactly two output
occurrences. Both A2 and A3 are automatic at length two, and the kept
supreme label supplies A1. Thus every such strict plan yields an
acceptable output without a freshness or linearity hypothesis.

This proves the order-one case only. Arbitrary replacement composition,
the length-two order-two case, and the general girth theorem are separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At order one no long piece can occur: its two source connector
boundaries would both be vertices, contradicting the mixed-kind
condition for every adjacent pair. -/
theorem BigCycle.plan_shortOnly_of_orderOne
    {n : ℕ} (C : D.BigCycle n)
    (hOrder : C.twiceOrder = 2)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    ∀ i : Fin n, (pieces i).IsShortOrKeep := by
  intro i
  cases hp : pieces i with
  | keep =>
      simp [TrainSupremePiece.IsShortOrKeep, hp]
  | short e =>
      simp [TrainSupremePiece.IsShortOrKeep, hp]
  | long e w f =>
      have hLong : C.LongValid D k i e w f :=
        C.longValid_of_piece_eq_long D k i pieces hPlan e f w hp
      obtain ⟨x, y, hx, hy, _he, _hf, _hne, _hpe, _hpf,
        _hxe, _hyf, _hNoPair⟩ := hLong
      have hMixed := C.connectors_mixed_of_order_one D hOrder
        (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i] at hMixed
      have hSame :
          connectorKind (C.connector (trainCyclicPred i)) =
            connectorKind (C.connector i) := by
        rw [hx, hy]
      exact False.elim (hMixed hSame)

/-- A short-only plan contributes exactly one output entry per source
occurrence, with no insertions. -/
theorem BigCycle.resultWord_length_of_shortOnly
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hShort : ∀ i : Fin n, (pieces i).IsShortOrKeep) :
    (C.resultWord D pieces).length = n := by
  classical
  have h : (∑ i : Fin n, (C.pieceWord D i (pieces i)).length) =
      ∑ i : Fin n, (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.pieceWord, hp]
    | short e =>
        simp [BigCycle.pieceWord, hp]
    | long e p f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using hShort i
        exact False.elim hf
  simpa [BigCycle.resultWord, List.length_flatten,
    List.sum_ofFn, List.map_ofFn] using h

/-- A genuine strict PlanValid replacement of an order-one acceptable
cycle always assembles into another acceptable two-occurrence BigCycle.
Neither output acceptability nor wagon linearity is assumed. -/
theorem BigCycle.planProducesAcceptable_of_orderOne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hOrder : C.twiceOrder = 2)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧
      List.ofFn (fun i : Fin m => (B.label i, B.connector i)) =
        C.resultWord D pieces := by
  have hShort := C.plan_shortOnly_of_orderOne D hOrder k pieces hPlan
  obtain ⟨m, B, hWord⟩ :=
    C.planProducesBigCycle_of_shortOnly
      D hAccept k hk pieces hPlan hShort
  have hn : n = 2 := C.length_eq_two_of_order_one D hOrder
  have hm : m = 2 := by
    have hLen := congrArg List.length hWord
    have hShortLen := C.resultWord_length_of_shortOnly D pieces hShort
    simpa [hShortLen, hn] using hLen
  subst m
  refine ⟨2, B, ?_, hWord⟩
  exact ⟨C.output_A1_of_kept_supreme D B k hk pieces hPlan hWord,
    D.twoCycle_A2 B, D.twoCycle_A3 B⟩

end StructuralRamsey.Girth.OrderOneData
