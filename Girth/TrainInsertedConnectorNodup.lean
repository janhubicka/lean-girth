import Girth.TrainCheckedCycleWord
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
      · exact Or.inr ⟨fresh, hi, heq⟩
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

end StructuralRamsey.Girth
