import Girth.TrainThreeWordCycle
import Girth.TrainStrictPlanAcceptability
import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

/-!
# Circulation: complete strict replacement at source length two

A strict PlanValid replacement keeps the chosen designated label.
At source length two, therefore, at most one piece is long. If no
piece is long, the checked short-only theorem assembles the output.

For the remaining case, there are exactly three literal output
entries: two actual edge labels separated by the fresh wagon
connector, and the kept designated label. The checked three-word
constructor verifies all cyclic label, incidence and injectivity
conditions, including wraparound.

The final theorem combines this literal existence at length two
with the checked >=3 construction and the all-length conditional
A1--A3 transfer. Numerical order and arbitrary composition are not
asserted. No appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At length two, every strict fresh PlanValid plan produces an
actual BigCycle, including the one-long-piece case. -/
theorem BigCycle.planProducesBigCycle_of_two
    (C : D.BigCycle 2)
    (hAccept : C.Acceptable)
    (k : Fin 2) (hk : D.designated (C.label k))
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin 2) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin 2, C.connector t ≠ Sum.inr p) :
    C.PlanProducesBigCycle D pieces := by
  have hConnNe : C.connector (0 : Fin 2) ≠ C.connector (1 : Fin 2) := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (C.connector_injective h)
  fin_cases k
  · have hKeep : pieces (0 : Fin 2) = .keep := (hPlan 0).1 rfl
    cases hp : pieces (1 : Fin 2) with
    | keep =>
        have hneq : C.label (1 : Fin 2) ≠ C.label (0 : Fin 2) := by
          simpa [cyclicSucc] using (C.adjacent_ne (0 : Fin 2)).symm
        have hf : False := by
          simpa [hp] using (hPlan 1).2 hneq
        exact False.elim hf
    | short e =>
        have hShort : ∀ j : Fin 2, (pieces j).IsShortOrKeep := by
          intro j
          fin_cases j
          · simp [TrainSupremePiece.IsShortOrKeep, hKeep]
          · simp [TrainSupremePiece.IsShortOrKeep, hp]
        exact C.planProducesBigCycle_of_shortOnly
          D hAccept 0 hk pieces hPlan hShort
    | long e p f =>
        have hLong : C.LongValid D 0 1 e p f :=
          C.longValid_of_piece_eq_long D 0 1 pieces hPlan e f p hp
        obtain ⟨x, y, hx, hy, _he, _hf, hne,
          hpe, hpf, hxe, hyf, _hNoPair⟩ := hLong
        have hx0 : C.connector (0 : Fin 2) = Sum.inl x := by
          simpa [trainCyclicPred] using hx
        have hye : D.Incident (.inr f) (C.connector (1 : Fin 2)) := by
          rw [hy]
          exact hyf
        have hxe0 : D.Incident (.inr e) (C.connector (0 : Fin 2)) := by
          rw [hx0]
          exact hxe
        have hAe : C.label (0 : Fin 2) ≠ (Sum.inr e : I ⊕ E) :=
          D.designated_ne_actualEdge (C.label 0) e hk
        have hAf : C.label (0 : Fin 2) ≠ (Sum.inr f : I ⊕ E) :=
          D.designated_ne_actualEdge (C.label 0) f hk
        have hef : (Sum.inr e : I ⊕ E) ≠ Sum.inr f := by
          intro h
          exact hne (Sum.inr.inj h)
        have hEa : D.Incident (.inr e) (Sum.inr p) :=
          ⟨e, rfl, hpe⟩
        have hFa : D.Incident (.inr f) (Sum.inr p) :=
          ⟨f, rfl, hpf⟩
        have hAw : D.Incident (C.label (0 : Fin 2))
            (C.connector (1 : Fin 2)) := by
          simpa [cyclicSucc] using C.right_incident (1 : Fin 2)
        obtain ⟨B, hB⟩ := D.threeWordBigCycle
          (C.label 0) (.inr e) (.inr f)
          (C.connector 0) (.inr p) (C.connector 1)
          hAe hef hAf.symm
          (hFresh 1 e p f hp 0)
          (hFresh 1 e p f hp 1).symm
          hConnNe.symm
          (C.left_incident 0) hEa hye
          hxe0 hFa hAw
        have hLiteral :
            C.resultWord D pieces =
              [(C.label 0, C.connector 0),
               (.inr e, .inr p), (.inr f, C.connector 1)] := by
          simp [BigCycle.resultWord, BigCycle.pieceWord,
            List.ofFn_succ, hKeep, hp]
        refine ⟨3, B, ?_⟩
        rw [hLiteral]
        exact hB
  · have hKeep : pieces (1 : Fin 2) = .keep := (hPlan 1).1 rfl
    cases hp : pieces (0 : Fin 2) with
    | keep =>
        have hneq : C.label (0 : Fin 2) ≠ C.label (1 : Fin 2) := by
          simpa [cyclicSucc] using C.adjacent_ne (0 : Fin 2)
        have hf : False := by
          simpa [hp] using (hPlan 0).2 hneq
        exact False.elim hf
    | short e =>
        have hShort : ∀ j : Fin 2, (pieces j).IsShortOrKeep := by
          intro j
          fin_cases j
          · simp [TrainSupremePiece.IsShortOrKeep, hp]
          · simp [TrainSupremePiece.IsShortOrKeep, hKeep]
        exact C.planProducesBigCycle_of_shortOnly
          D hAccept 1 hk pieces hPlan hShort
    | long e p f =>
        have hLong : C.LongValid D 1 0 e p f :=
          C.longValid_of_piece_eq_long D 1 0 pieces hPlan e f p hp
        obtain ⟨x, y, hx, hy, _he, _hf, hne,
          hpe, hpf, hxe, hyf, _hNoPair⟩ := hLong
        have hx1 : C.connector (1 : Fin 2) = Sum.inl x := by
          simpa [trainCyclicPred] using hx
        have hye0 : D.Incident (.inr f) (C.connector (0 : Fin 2)) := by
          rw [hy]
          exact hyf
        have hxe1 : D.Incident (.inr e) (C.connector (1 : Fin 2)) := by
          rw [hx1]
          exact hxe
        have hAe : C.label (1 : Fin 2) ≠ (Sum.inr e : I ⊕ E) :=
          D.designated_ne_actualEdge (C.label 1) e hk
        have hAf : C.label (1 : Fin 2) ≠ (Sum.inr f : I ⊕ E) :=
          D.designated_ne_actualEdge (C.label 1) f hk
        have hef : (Sum.inr e : I ⊕ E) ≠ Sum.inr f := by
          intro h
          exact hne (Sum.inr.inj h)
        have hEa : D.Incident (.inr e) (Sum.inr p) :=
          ⟨e, rfl, hpe⟩
        have hFa : D.Incident (.inr f) (Sum.inr p) :=
          ⟨f, rfl, hpf⟩
        have hAv : D.Incident (C.label (1 : Fin 2))
            (C.connector (0 : Fin 2)) := by
          simpa [cyclicSucc] using C.right_incident (1 : Fin 2)
        obtain ⟨B, hB⟩ := D.threeWordBigCycle
          (.inr e) (.inr f) (C.label 1)
          (.inr p) (C.connector 0) (C.connector 1)
          hef hAf.symm hAe
          (hFresh 0 e p f hp 0).symm
          hConnNe
          (hFresh 0 e p f hp 1)
          hEa hye0 (C.left_incident 1)
          hFa hAv hxe1
        have hLiteral :
            C.resultWord D pieces =
              [(.inr e, .inr p), (.inr f, C.connector 0),
               (C.label 1, C.connector 1)] := by
          simp [BigCycle.resultWord, BigCycle.pieceWord,
            List.ofFn_succ, hKeep, hp]
        refine ⟨3, B, ?_⟩
        rw [hLiteral]
        exact hB

/-- Every fresh strict PlanValid replacement of an acceptable big
cycle in a linear pretrain produces an acceptable literal output at
ALL source lengths. The remaining numerical-order and arbitrary
composition assertions are not included. -/
theorem BigCycle.planProducesAcceptable_all_lengths
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
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
  by_cases hn : 3 ≤ n
  · exact C.planProducesAcceptable_of_fresh_long
      D hAccept hLinear hn k hk pieces hPlan hFresh
  · have hn2 : n = 2 := by
      have hlen := C.length_ge_two
      omega
    subst n
    obtain ⟨m, B, hWord⟩ :=
      C.planProducesBigCycle_of_two
        D hAccept k hk pieces hPlan hFresh
    exact ⟨m, B,
      C.output_acceptable_of_literal_resultWord
        D B hAccept hLinear k hk pieces hPlan hFresh hWord,
      hWord⟩

end StructuralRamsey.Girth.OrderOneData
