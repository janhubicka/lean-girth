import Girth.TrainInsertedConnectorNodup
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-!
# Circulation: the successor of a genuinely inserted wagon

A long-piece block of the literal replacement word has CONNECTORS
[fresh wagon, old source connector]. Every other block has only its
old source connector.

This module turns that elementary local pattern into an ordinary
List.IsChain theorem. Its binary relation remembers precisely the
useful fact: whenever a connector is a fresh insertion at source
position i, the NEXT connector in the non-wrapping expanded list
must be the old source connector i.

The proof uses the already checked optionalConnectorWord of #523,
Mathlib isChain_flatten, freshness against old connectors and
pairwise uniqueness of inserted wagons. No output BigCycle, A2/A3
transfer, output linearity or appendix hypothesis is assumed.

The cyclic-last-position exclusion and application to the physical
oldPos map are intentionally separate subsequent steps.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- If a fresh inserted connector a originated at i, its successor must
be the original source connector at i. Old connector tokens make the
antecedent false, so a chain may cross block boundaries freely. -/
def optionalFreshFollows
    (base : Fin n → α) (insert : Fin n → Option α)
    (a b : α) : Prop :=
  ∀ i : Fin n, insert i = some a → b = base i

/-- The last connector of every optional-insertion block is exactly
the original source connector, whether or not a fresh wagon is present. -/
theorem optionalConnectorBlock_last?
    (base : Fin n → α) (insert : Fin n → Option α)
    (i : Fin n) :
    (optionalConnectorBlock base insert i).getLast? = some (base i) := by
  cases hi : insert i with
  | none => simp [optionalConnectorBlock, hi]
  | some fresh => simp [optionalConnectorBlock, hi]

/-- The entire literal expanded connector word is a noncyclic chain
of the fresh-to-original successor relation. The only nontrivial
inside-block condition is uniqueness of the fresh wagon across
source positions; every between-block condition is vacuous by
freshness relative to all old connectors. -/
theorem optionalConnectorWord_freshSuccessor_chain
    (base : Fin n → α) (insert : Fin n → Option α)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j)
    (hDifferent : ∀ (i j : Fin n) (a b : α),
      i ≠ j → insert i = some a → insert j = some b → a ≠ b) :
    (optionalConnectorWord base insert).IsChain
      (optionalFreshFollows base insert) := by
  classical
  unfold optionalConnectorWord
  have hNonempty :
      ([] : List α) ∉
        List.ofFn (fun i : Fin n => optionalConnectorBlock base insert i) := by
    intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    cases hIns : insert i with
    | none => simp [optionalConnectorBlock, hIns] at hi
    | some fresh => simp [optionalConnectorBlock, hIns] at hi
  apply (List.isChain_flatten hNonempty).mpr
  constructor
  · intro block hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    cases hIns : insert i with
    | none =>
        simp [optionalConnectorBlock, hIns]
    | some a =>
        have hInside : optionalFreshFollows base insert a (base i) := by
          intro j hj
          by_cases hij : i = j
          · subst j
            rfl
          · exact False.elim
              ((hDifferent i j a a hij hIns hj) rfl)
        simpa [optionalConnectorBlock, hIns]
          using (List.isChain_pair.mpr hInside)
  · rw [List.isChain_ofFn]
    intro t ht
    let i : Fin n := ⟨t, Nat.lt_of_succ_lt ht⟩
    have hBoundary :
        ∀ᵉ (x ∈ (optionalConnectorBlock base insert i).getLast?)
            (y ∈ (optionalConnectorBlock base insert ⟨t + 1, ht⟩).head?),
          optionalFreshFollows base insert x y := by
      intro x hx y _hy
      have hEq : x = base i := by
        have hx' : base i = x := by
          simpa [optionalConnectorBlock_last?] using hx
        exact hx'.symm
      subst x
      intro j hj
      exact False.elim ((hFresh j i (base i) hj) rfl)
    simpa [List.get_ofFn, i] using hBoundary

/-- A fresh connector at an output index which is not the last index
is followed immediately by its uniquely specified original source
connector. The cyclic-last case will be excluded by a separate
last-block lemma before this is applied to the output BigCycle. -/
theorem optionalConnectorWord_fresh_successor_of_nonlast
    (base : Fin n → α) (insert : Fin n → Option α)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j)
    (hDifferent : ∀ (i j : Fin n) (a b : α),
      i ≠ j → insert i = some a → insert j = some b → a ≠ b)
    (i : Fin n) (a : α) (hi : insert i = some a)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = a)
    (hNext : j.val + 1 < (optionalConnectorWord base insert).length) :
    (optionalConnectorWord base insert).get
        ⟨j.val + 1, hNext⟩ = base i := by
  have hChain := optionalConnectorWord_freshSuccessor_chain
    base insert hFresh hDifferent
  have hRel :
      optionalFreshFollows base insert
        ((optionalConnectorWord base insert).get j)
        ((optionalConnectorWord base insert).get
          ⟨j.val + 1, hNext⟩) := by
    simpa using (List.isChain_iff_getElem.mp hChain) j.val hNext
  rw [hj] at hRel
  exact hRel i hi

end StructuralRamsey.Girth
