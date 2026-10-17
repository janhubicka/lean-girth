import Girth.TrainShortOnlyPlanGlobal
import Girth.TrainShortReplacementAcceptability
import Girth.TrainOutputA1Length
import Girth.TrainInsertedConnectorNodup
import Mathlib.Tactic

/-!
# Circulation: literal short-only replacements preserve acceptability and order

When a strict plan contains no long pieces, each replacement block has
exactly one entry with its ORIGINAL connector. Hence the connector
projection of the flattened literal output word is exactly the old
connector list, not merely a permutation of its members.

Any actual output BigCycle therefore has the same number of positions
and pointwise the same connectors. The existing connector-invariant
A2/A3 lemmas apply, the kept supreme label gives A1, and the numerical
twice-order agrees exactly. This covers every source length including two,
without assuming output acceptability or any wagon linearity.

No appendix theorem and no arbitrary mixed-plan composition are used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The connector projection of a genuine short-only literal resultWord
is exactly the source connector list, with no index permutation. -/
theorem BigCycle.shortOnly_resultWord_connectorList
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hShort : ∀ i : Fin n, (pieces i).IsShortOrKeep) :
    (C.resultWord D pieces).map Prod.snd =
      List.ofFn C.connector := by
  rw [C.resultWord_connectorList D pieces]
  unfold optionalConnectorWord
  have hBlocks :
      List.ofFn (fun i : Fin n =>
        optionalConnectorBlock C.connector (C.insertedConnector D pieces) i) =
      List.ofFn (fun i : Fin n => [C.connector i]) := by
    apply congrArg List.ofFn
    funext i
    cases hp : pieces i with
    | keep =>
        simp [optionalConnectorBlock, BigCycle.insertedConnector, hp]
    | short e =>
        simp [optionalConnectorBlock, BigCycle.insertedConnector, hp]
    | long e p f =>
        have hf : False := by
          simpa [TrainSupremePiece.IsShortOrKeep, hp] using hShort i
        exact False.elim hf
  rw [hBlocks]
  exact flatten_ofFn_singleton C.connector

/-- Pointwise equality of the source and literal output connectors
transports complete acceptability and numerical twice-order at once,
with the only A1 input being retention of the supreme label. -/
theorem BigCycle.output_acceptable_order_of_shortOnly
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hShort : ∀ i : Fin n, (pieces i).IsShortOrKeep)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  have hProjection : List.ofFn B.connector = List.ofFn C.connector := by
    calc
      List.ofFn B.connector =
          (List.ofFn (fun j : Fin m =>
            (B.label j, B.connector j))).map Prod.snd := by
              simp [List.map_ofFn, Function.comp_def]
      _ = (C.resultWord D pieces).map Prod.snd :=
            congrArg (List.map Prod.snd) hWord
      _ = List.ofFn C.connector :=
            C.shortOnly_resultWord_connectorList D pieces hShort
  have hLen : m = n := by
    have h := congrArg List.length hProjection
    simpa using h
  cases hLen
  have hConnector : ∀ i : Fin n, B.connector i = C.connector i := by
    intro i
    have hAt := congrArg
      (fun xs : List (V ⊕ P) => xs[i.val]?) hProjection
    have hB : (List.ofFn B.connector)[i.val]? =
        some (B.connector i) := by
      simp [List.get_ofFn]
    have hC : (List.ofFn C.connector)[i.val]? =
        some (C.connector i) := by
      simp [List.get_ofFn]
    exact Option.some.inj (hB.symm.trans (hAt.trans hC))
  have hA1 : B.A1 :=
    C.output_A1_of_kept_supreme D B k hk pieces hPlan hWord
  refine ⟨⟨hA1,
      C.A2_of_same_connectors D B hConnector hAccept.2.1,
      C.A3_of_same_connectors D B hConnector hAccept.2.2⟩, ?_⟩
  exact C.twiceOrder_eq_of_same_connectors D B hConnector

/-- A short-only strict PlanValid plan automatically produces a legal
acceptable output of exactly the same numerical order. -/
theorem BigCycle.planProducesAcceptableOrder_of_shortOnly
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hShort : ∀ i : Fin n, (pieces i).IsShortOrKeep) :
    ∃ m : ℕ, ∃ B : D.BigCycle m,
      B.Acceptable ∧ B.twiceOrder = C.twiceOrder ∧
      List.ofFn (fun i : Fin m => (B.label i, B.connector i)) =
        C.resultWord D pieces := by
  obtain ⟨m, B, hWord⟩ :=
    C.planProducesBigCycle_of_shortOnly
      D hAccept k hk pieces hPlan hShort
  obtain ⟨hOut, hOrder⟩ :=
    C.output_acceptable_order_of_shortOnly
      D B hAccept k hk pieces hPlan hShort hWord
  exact ⟨m, B, hOut, hOrder, hWord⟩

end StructuralRamsey.Girth.OrderOneData
