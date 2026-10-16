import Girth.TrainTwoLongOutputAccept
import Girth.TrainInsertedConnectorNodup
import Girth.TrainShortReplacementAcceptability
import Girth.TrainOutputA1Length
import Mathlib.Tactic

/-!
# Circulation: complete length-two source replacement acceptability and order

The two-occurrence case of the general replacement argument separates
into (i) short-only plans, whose original connector sequence is unchanged,
and (ii) one long piece next to the retained designated occurrence.
Both long-piece orientations have already been checked in the stacked
two-to-three output lemma.

This file composes those alternatives for the ACTUAL replacement word:
the output must satisfy A1--A3 and preserve the source numerical order,
without assuming output wagon linearity or global A2/A3 transfer.

The length-at-least-three source case and broad arbitrary-retained-label
composition remain separate. No appendix claims are used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- With no long pieces, even a length-two source has precisely its
old connector list in the ACTUAL flattened output.  Consequently any
literal output BigCycle is A1--A3 acceptable and order preserving. -/
theorem BigCycle.two_short_only_output_accept_order
    (C : D.BigCycle 2) {m : ℕ} (B : D.BigCycle m)
    (k : Fin 2) (hk : D.designated (C.label k))
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hShortOnly : ∀ i, (pieces i).IsShortOrKeep)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  have hNone (i : Fin 2) :
      C.insertedConnector D pieces i = none := by
    cases hp : pieces i with
    | keep => simp [BigCycle.insertedConnector, hp]
    | short e => simp [BigCycle.insertedConnector, hp]
    | long e p f =>
        have hBad := hShortOnly i
        simp [TrainSupremePiece.IsShortOrKeep, hp] at hBad
  have hConnList :
      (C.resultWord D pieces).map Prod.snd =
        List.ofFn C.connector := by
    rw [C.resultWord_connectorList D pieces]
    have h0 := hNone (0 : Fin 2)
    have h1 := hNone (1 : Fin 2)
    simp [optionalConnectorWord, optionalConnectorBlock,
      List.ofFn_succ, List.ofFn_zero, h0, h1]
  have hm : m = 2 := by
    have hLenOut : (C.resultWord D pieces).length = 2 := by
      have h := congrArg List.length hConnList
      simpa using h
    have h := congrArg List.length hWord
    simpa [hLenOut] using h
  subst m
  have hBConnList : List.ofFn B.connector = List.ofFn C.connector := by
    calc
      List.ofFn B.connector =
          (List.ofFn (fun i : Fin 2 => (B.label i, B.connector i))).map Prod.snd := by
            simp [List.ofFn_comp']
      _ = (C.resultWord D pieces).map Prod.snd :=
        congrArg (List.map Prod.snd) hWord
      _ = List.ofFn C.connector := hConnList
  have hConn (i : Fin 2) : B.connector i = C.connector i := by
    fin_cases i
    · have h := congrArg
        (fun l : List (V ⊕ P) => l[0]?) hBConnList
      simpa [List.ofFn_succ, List.ofFn_zero] using h
    · have h := congrArg
        (fun l : List (V ⊕ P) => l[1]?) hBConnList
      simpa [List.ofFn_succ, List.ofFn_zero] using h
  have hA1 : B.A1 :=
    C.output_A1_of_kept_supreme D B k hk pieces hPlan hWord
  exact ⟨⟨hA1, D.twoCycle_A2 B, D.twoCycle_A3 B⟩,
    C.twiceOrder_eq_of_same_connectors D B hConn⟩

/-- Full length-two source case, for any actual PlanValid supreme plan
and its literally assembled result word. Short pieces preserve the
original two-connector order; one long piece yields one of the two
checked acceptable three-cycles. -/
theorem BigCycle.two_plan_output_accept_order
    (C : D.BigCycle 2) {m : ℕ} (B : D.BigCycle m)
    (k : Fin 2) (hk : D.designated (C.label k))
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  fin_cases k
  · have hKeep : pieces 0 = .keep := (hPlan 0).1 rfl
    have hne : C.label 1 ≠ C.label 0 := by
      simpa [cyclicSucc] using C.adjacent_ne 1
    have hOther := (hPlan 1).2 hne
    cases hp : pieces 1 with
    | keep =>
        simp [hp] at hOther
    | short e =>
        have hShortOnly : ∀ i : Fin 2, (pieces i).IsShortOrKeep := by
          intro i
          fin_cases i
          · simpa [hKeep, TrainSupremePiece.IsShortOrKeep]
          · simpa [hp, TrainSupremePiece.IsShortOrKeep]
        exact C.two_short_only_output_accept_order D B 0 hk
          pieces hPlan hShortOnly hWord
    | long e w f =>
        have hv : C.LongValid D 0 1 e w f := by
          simpa [hp] using hOther
        have hm : m = 3 := by
          have h := congrArg List.length hWord
          simpa [BigCycle.resultWord, BigCycle.pieceWord,
            hKeep, hp, List.ofFn_succ, List.ofFn_zero] using h
        subst m
        exact C.two_keep0_long1_output_accept_order D B pieces
          hKeep e f w hp hv hWord
  · have hKeep : pieces 1 = .keep := (hPlan 1).1 rfl
    have hne : C.label 0 ≠ C.label 1 := C.adjacent_ne 0
    have hOther := (hPlan 0).2 hne
    cases hp : pieces 0 with
    | keep =>
        simp [hp] at hOther
    | short e =>
        have hShortOnly : ∀ i : Fin 2, (pieces i).IsShortOrKeep := by
          intro i
          fin_cases i
          · simpa [hp, TrainSupremePiece.IsShortOrKeep]
          · simpa [hKeep, TrainSupremePiece.IsShortOrKeep]
        exact C.two_short_only_output_accept_order D B 1 hk
          pieces hPlan hShortOnly hWord
    | long e w f =>
        have hv : C.LongValid D 1 0 e w f := by
          simpa [hp] using hOther
        have hm : m = 3 := by
          have h := congrArg List.length hWord
          simpa [BigCycle.resultWord, BigCycle.pieceWord,
            hKeep, hp, List.ofFn_succ, List.ofFn_zero] using h
        subst m
        exact C.two_long0_keep1_output_accept_order D B pieces
          hKeep e f w hp hv hWord

end StructuralRamsey.Girth.OrderOneData
