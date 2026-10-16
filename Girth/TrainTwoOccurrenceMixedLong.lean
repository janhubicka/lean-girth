import Girth.TrainPlanCyclicWrap
import Girth.TrainShortOnlyPlanGlobal
import Mathlib.Tactic

/-!
# Circulation: the two-occurrence mixed long replacement

The generic global mixed-plan theorem is already verified for source cycles
with at least three occurrences. At source length two, PlanValid preserves
its selected designated occurrence, so only the OTHER occurrence may be
replaced. That occurrence is either short (covered by the checked
short-only global theorem) or long.

A single long replacement gives an explicit three-occurrence cycle:
  kept label, first edge, second edge
or its cyclic rotation. The fresh wagon is between two original
vertex connectors, and the nonedge clause of LongValid makes the two
physical edges distinct. The kept designated label differs from both
physical edge labels by the disjoint sum of labels.

The source length-two A2 and A3 predicates are automatic, and no
linearity of an assembled output is needed. The first two lemmas
construct the ACTUAL BigCycle and exact flattened word in both cases.

A successful result removes the length-three restriction from literal
mixed-plan legality. It does NOT transfer output A2/A3 acceptability,
numeric order, or supreme collapse composition.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A kept source occurrence 0 followed by a long replacement of
occurrence 1 forms a literal three-occurrence output BigCycle. -/
theorem BigCycle.two_keep0_long1_global
    (C : D.BigCycle 2)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hKeep : pieces 0 = .keep)
    (e f : E) (w : P)
    (hLong : pieces 1 = .long e w f)
    (hk : D.designated (C.label 0))
    (hValid : C.LongValid D 0 1 e w f) :
    C.PlanProducesBigCycle D pieces := by
  obtain ⟨x, y, hPrev, hHere, he, hf, hef, hew, hfw,
    hxe, hyf, hNoPair⟩ := hValid
  have hx : C.connector 0 = Sum.inl x := by
    simpa [trainCyclicPred] using hPrev
  have hy : C.connector 1 = Sum.inl y := hHere
  have hxy : x ≠ y := by
    intro h
    have hc : C.connector (0 : Fin 2) = C.connector 1 := by
      rw [hx, hy, h]
    have hidx : (0 : Fin 2) = 1 := C.connector_injective hc
    exact (by decide : (0 : Fin 2) ≠ 1) hidx
  let B : D.BigCycle 3 := {
    length_ge_two := by omega
    label := ![C.label 0, Sum.inr e, Sum.inr f]
    connector := ![C.connector 0, Sum.inr w, C.connector 1]
    adjacent_ne := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using
          (D.designated_ne_actualEdge (C.label 0) e hk)
      · simpa [cyclicSucc] using
          (show (Sum.inr e : I ⊕ E) ≠ Sum.inr f from
            fun h => hef (Sum.inr.inj h))
      · simpa [cyclicSucc] using
          (D.designated_ne_actualEdge (C.label 0) f hk).symm
    connector_injective := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp_all [hx, hy, hxy]
    left_incident := by
      intro i
      fin_cases i
      · exact C.left_incident 0
      · exact ⟨e, rfl, hew⟩
      · simpa [hy, Incident] using hyf
    right_incident := by
      intro i
      fin_cases i
      · simpa [cyclicSucc, hx, Incident] using hxe
      · simpa [cyclicSucc, Incident] using
          (show D.Meets (.inr f) w from ⟨f, rfl, hfw⟩)
      · simpa [cyclicSucc] using C.right_incident 1
  }
  refine ⟨3, B, ?_⟩
  simp [BigCycle.resultWord, BigCycle.pieceWord,
    hKeep, hLong, B, List.ofFn_succ, List.ofFn_zero]

/-- A long replacement of source occurrence 0 followed by a kept
designated occurrence 1 gives the cyclically rotated three-word. -/
theorem BigCycle.two_long0_keep1_global
    (C : D.BigCycle 2)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hKeep : pieces 1 = .keep)
    (e f : E) (w : P)
    (hLong : pieces 0 = .long e w f)
    (hk : D.designated (C.label 1))
    (hValid : C.LongValid D 1 0 e w f) :
    C.PlanProducesBigCycle D pieces := by
  obtain ⟨x, y, hPrev, hHere, he, hf, hef, hew, hfw,
    hxe, hyf, hNoPair⟩ := hValid
  have hx : C.connector 1 = Sum.inl x := by
    simpa [trainCyclicPred] using hPrev
  have hy : C.connector 0 = Sum.inl y := hHere
  have hxy : x ≠ y := by
    intro h
    have hc : C.connector (0 : Fin 2) = C.connector 1 := by
      rw [hy, hx, h]
    have hidx : (0 : Fin 2) = 1 := C.connector_injective hc
    exact (by decide : (0 : Fin 2) ≠ 1) hidx
  let B : D.BigCycle 3 := {
    length_ge_two := by omega
    label := ![Sum.inr e, Sum.inr f, C.label 1]
    connector := ![Sum.inr w, C.connector 0, C.connector 1]
    adjacent_ne := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using
          (show (Sum.inr e : I ⊕ E) ≠ Sum.inr f from
            fun h => hef (Sum.inr.inj h))
      · simpa [cyclicSucc] using
          (D.designated_ne_actualEdge (C.label 1) f hk).symm
      · simpa [cyclicSucc] using
          (D.designated_ne_actualEdge (C.label 1) e hk)
    connector_injective := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp_all [hx, hy, hxy]
    left_incident := by
      intro i
      fin_cases i
      · exact ⟨e, rfl, hew⟩
      · simpa [hy, Incident] using hyf
      · exact C.left_incident 1
    right_incident := by
      intro i
      fin_cases i
      · simpa [cyclicSucc, Incident] using
          (show D.Meets (.inr f) w from ⟨f, rfl, hfw⟩)
      · simpa [cyclicSucc] using C.right_incident 0
      · simpa [cyclicSucc, hx, Incident] using hxe
  }
  refine ⟨3, B, ?_⟩
  simp [BigCycle.resultWord, BigCycle.pieceWord,
    hKeep, hLong, B, List.ofFn_succ, List.ofFn_zero]

/-- The two-occurrence case of global PlanValid legality. The sole
non-kept occurrence is short (existing theorem) or long (the explicit
three-occurrence constructions above). -/
theorem BigCycle.planProducesBigCycle_two_of_fresh_long
    (C : D.BigCycle 2)
    (k : Fin 2) (hk : D.designated (C.label k))
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    C.PlanProducesBigCycle D pieces := by
  have hAccept : C.Acceptable := by
    exact ⟨(by intro _; exact ⟨k, hk⟩),
      D.twoCycle_A2 C, D.twoCycle_A3 C⟩
  fin_cases k
  · have hKeep : pieces 0 = .keep := (hPlan 0).1 rfl
    have hne : C.label 1 ≠ C.label 0 := by
      simpa [cyclicSucc] using (C.adjacent_ne 1)
    have hOther := (hPlan 1).2 hne
    cases hp : pieces 1 with
    | keep =>
        simp [hp] at hOther
    | short e =>
        have hShortOnly : ∀ j : Fin 2, (pieces j).IsShortOrKeep := by
          intro j
          fin_cases j
          · simpa [hKeep, TrainSupremePiece.IsShortOrKeep]
          · simpa [hp, TrainSupremePiece.IsShortOrKeep]
        exact C.planProducesBigCycle_of_shortOnly D
          hAccept 0 hk pieces hPlan hShortOnly
    | long e w f =>
        have hv : C.LongValid D 0 1 e w f := by
          simpa [hp] using hOther
        exact C.two_keep0_long1_global D pieces hKeep e f w hp hk hv
  · have hKeep : pieces 1 = .keep := (hPlan 1).1 rfl
    have hne : C.label 0 ≠ C.label 1 := by
      exact C.adjacent_ne 0
    have hOther := (hPlan 0).2 hne
    cases hp : pieces 0 with
    | keep =>
        simp [hp] at hOther
    | short e =>
        have hShortOnly : ∀ j : Fin 2, (pieces j).IsShortOrKeep := by
          intro j
          fin_cases j
          · simpa [hp, TrainSupremePiece.IsShortOrKeep]
          · simpa [hKeep, TrainSupremePiece.IsShortOrKeep]
        exact C.planProducesBigCycle_of_shortOnly D
          hAccept 1 hk pieces hPlan hShortOnly
    | long e w f =>
        have hv : C.LongValid D 1 0 e w f := by
          simpa [hp] using hOther
        exact C.two_long0_keep1_global D pieces hKeep e f w hp hk hv

end StructuralRamsey.Girth.OrderOneData
