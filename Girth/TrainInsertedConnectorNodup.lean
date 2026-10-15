import Girth.TrainCheckedCycleWord
import Girth.TrainLongBoundaryCollision
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

/-!
# Circulation: optional fresh connector insertions preserve distinctness

The global replacement word retains the original connector after every
old occurrence. A long piece additionally inserts exactly one new wagon
connector immediately before that old connector. Short/keep pieces
insert nothing.

This module first formalizes the PURE finite-list fact needed here:
if old connectors are injective, every inserted connector is different
from every old connector, and insertions at distinct positions differ,
then the flattened list of optional insertions is duplicate-free.

The result uses no girth assumptions or output BigCycle. The intended
application is to source connector injectivity and checked #520
pairwise freshness of long-piece wagons. The corresponding label and
incidence checks remain separate.

No appendix theorem is involved.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- One retained old connector, optionally preceded by a new connector. -/
def optionalConnectorBlock
    (base : Fin n → α) (insert : Fin n → Option α)
    (i : Fin n) : List α :=
  match insert i with
  | none => [base i]
  | some new => [new, base i]

/-- Concatenation of the original connectors with optional insertions. -/
def optionalConnectorWord
    (base : Fin n → α) (insert : Fin n → Option α) : List α :=
  (List.ofFn fun i : Fin n => optionalConnectorBlock base insert i).flatten

/-- Membership in a block: the connector is old, or exactly the fresh
connector inserted at this position. -/
theorem optionalConnectorBlock_mem_cases
    (base : Fin n → α) (insert : Fin n → Option α)
    (i : Fin n) (x : α)
    (hx : x ∈ optionalConnectorBlock base insert i) :
    x = base i ∨ ∃ fresh, insert i = some fresh ∧ x = fresh := by
  cases hi : insert i with
  | none =>
      have heq : x = base i := by
        simpa [optionalConnectorBlock, hi] using hx
      exact Or.inl heq
  | some fresh =>
      have heq : x = fresh ∨ x = base i := by
        simpa [optionalConnectorBlock, hi] using hx
      rcases heq with heq | heq
      · exact Or.inr ⟨fresh, rfl, heq⟩
      · exact Or.inl heq

/-- The old connectors remain distinct after inserting arbitrary fresh
tokens at arbitrary different positions. This is a finite word theorem,
not an output-girth or constructed-cycle hypothesis. -/
theorem optionalConnectorWord_nodup
    (base : Fin n → α) (insert : Fin n → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j)
    (hDifferent : ∀ (i j : Fin n) (a b : α),
      i ≠ j → insert i = some a → insert j = some b → a ≠ b) :
    (optionalConnectorWord base insert).Nodup := by
  classical
  unfold optionalConnectorWord
  rw [List.nodup_flatten]
  constructor
  · intro block hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    cases hi : insert i with
    | none =>
        simp [optionalConnectorBlock, hi]
    | some a =>
        have hne : a ≠ base i := hFresh i i a hi
        simp [optionalConnectorBlock, hi, hne]
  · rw [List.pairwise_ofFn]
    intro i j hij
    rw [List.disjoint_left]
    intro x hxi hxj
    have hi := optionalConnectorBlock_mem_cases base insert i x hxi
    have hj := optionalConnectorBlock_mem_cases base insert j x hxj
    have hijne : i ≠ j := ne_of_lt hij
    rcases hi with hi | ⟨a, ha, hi⟩
    · rcases hj with hj | ⟨b, hb, hj⟩
      · exact hijne (hBase (hi.symm.trans hj))
      · exact hFresh j i b hb (hj.symm.trans hi)
    · rcases hj with hj | ⟨b, hb, hj⟩
      · exact hFresh i j a ha (hi.symm.trans hj)
      · exact hDifferent i j a b hijne ha hb (hi.symm.trans hj)


namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A long piece inserts its parent wagon immediately before its old right
connector. Short and retained pieces do not insert any connector. -/
def BigCycle.insertedConnector {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) (i : Fin n) :
    Option (V ⊕ P) :=
  match pieces i with
  | .long _ p _ => some (Sum.inr p)
  | .keep => none
  | .short _ => none

/-- The connector projection of the literal replacement word is exactly
the old connector list with optional fresh wagon connectors inserted.
This equality retains all cyclic positions, not merely the set of
connectors. -/
theorem BigCycle.resultWord_connectorList
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    (C.resultWord D pieces).map Prod.snd =
      optionalConnectorWord C.connector (C.insertedConnector D pieces) := by
  unfold BigCycle.resultWord optionalConnectorWord
  rw [List.map_flatten, ← List.ofFn_comp']
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  cases hp : pieces i with
  | keep =>
      simp [BigCycle.pieceWord, BigCycle.insertedConnector,
        optionalConnectorBlock, hp]
  | short e =>
      simp [BigCycle.pieceWord, BigCycle.insertedConnector,
        optionalConnectorBlock, hp]
  | long e p f =>
      simp [BigCycle.pieceWord, BigCycle.insertedConnector,
        optionalConnectorBlock, hp]

/-- Freshness and pairwise distinctness proved by #520 imply a genuine
Nodup property for the connector projection of the ACTUAL flattened
replacement word. This discharges the output connector-injectivity
requirement without assuming an output BigCycle. -/
theorem BigCycle.resultWord_connectors_nodup
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ((C.resultWord D pieces).map Prod.snd).Nodup := by
  rw [C.resultWord_connectorList D pieces]
  apply optionalConnectorWord_nodup
    C.connector (C.insertedConnector D pieces)
  · exact C.connector_injective
  · intro i j a hi
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at hi
    | short e =>
        simp [BigCycle.insertedConnector, hp] at hi
    | long e p f =>
        have ha : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using hi.symm
        subst a
        exact (hFresh i e p f hp j).symm
  · intro i j a b hij hi hj
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at hi
    | short e =>
        simp [BigCycle.insertedConnector, hp] at hi
    | long e p f =>
        have ha : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using hi.symm
        cases hq : pieces j with
        | keep =>
            simp [BigCycle.insertedConnector, hq] at hj
        | short g =>
            simp [BigCycle.insertedConnector, hq] at hj
        | long g q h =>
            have hb : b = (Sum.inr q : V ⊕ P) := by
              simpa [BigCycle.insertedConnector, hq] using hj.symm
            have hpq : p ≠ q :=
              C.plan_fresh_long_wagons_pairwise D hAccept hn k
                pieces hPlan hFresh i j hij e f g h p q hp hq
            intro hab
            apply hpq
            exact Sum.inr.inj (ha.symm.trans (hab.trans hb))

end OrderOneData
end StructuralRamsey.Girth
