import Girth.TrainOptionalFreshCyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-!
# Circulation: old connectors with no following insertion preserve successors

In the literal optional-insertion connector word, the last element of
every block is its OLD source connector. If the NEXT source block has
no fresh insertion, the next output connector must be the next OLD
source connector.

We express that statement as an ordinary List.IsChain relation. Within
a two-entry block the first token is fresh and so cannot be an old
connector; between source blocks the assertion follows from injectivity
of the source connector labels and the actual optional insertion at
the next block. This proves the non-wrapping successor relation without
an output BigCycle, A2/A3, or output linearity.

The cyclic wrap, its application to physical oldPos and inherited wagon
predecessor/successor equations remain subsequent steps.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- When an old connector is followed by a source block with NO insertion,
the next token must be the old source successor connector. For a fresh
token this relation is vacuous by source/fresh disjointness. -/
def optionalOldFollows (base : Fin n → α) (insert : Fin n → Option α)
    (a b : α) : Prop :=
  ∀ i : Fin n, a = base i → insert (cyclicSucc i) = none →
    b = base (cyclicSucc i)

/-- All non-wrapping adjacent positions in an optional-insertion word
satisfy the exact old-to-old successor condition. -/
theorem optionalConnectorWord_oldSuccessor_chain
    (base : Fin n → α) (insert : Fin n → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j) :
    (optionalConnectorWord base insert).IsChain
      (optionalOldFollows base insert) := by
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
    | some fresh =>
        have hInside :
            optionalOldFollows base insert fresh (base i) := by
          intro j hj _hNone
          exact False.elim ((hFresh i j fresh hIns) hj)
        simpa [optionalConnectorBlock, hIns]
          using (List.isChain_pair.mpr hInside)
  · rw [List.isChain_ofFn]
    intro t ht
    let i : Fin n := ⟨t, Nat.lt_of_succ_lt ht⟩
    let j : Fin n := ⟨t + 1, ht⟩
    have hSucc : cyclicSucc i = j := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt ht
    have hBoundary :
        ∀ᵉ (a ∈ (optionalConnectorBlock base insert i).getLast?)
            (b ∈ (optionalConnectorBlock base insert j).head?),
          optionalOldFollows base insert a b := by
      intro a ha b hb k hak hNext
      have haEq : a = base i := by
        have h : base i = a := by
          simpa [optionalConnectorBlock_last?] using ha
        exact h.symm
      have hki : k = i := hBase (hak.symm.trans haEq)
      have hNone : insert j = none := by
        simpa [hki, hSucc] using hNext
      have hbEq : b = base j := by
        simpa [optionalConnectorBlock, hNone] using hb.symm
      simpa [hki, hSucc] using hbEq
    simpa [List.get_ofFn, i, j] using hBoundary

/-- Every NON-LAST old connector with no following insertion has
exactly the next old connector at its next physical output position.
The last-to-first wrap is handled by a separate lemma. -/
theorem optionalConnectorWord_old_successor_of_nonlast
    (base : Fin n → α) (insert : Fin n → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j)
    (i : Fin n) (hNone : insert (cyclicSucc i) = none)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = base i)
    (hNext : j.val + 1 < (optionalConnectorWord base insert).length) :
    (optionalConnectorWord base insert).get
      ⟨j.val + 1, hNext⟩ = base (cyclicSucc i) := by
  have hChain :=
    optionalConnectorWord_oldSuccessor_chain base insert hBase hFresh
  have hRel : optionalOldFollows base insert
      ((optionalConnectorWord base insert).get j)
      ((optionalConnectorWord base insert).get ⟨j.val + 1, hNext⟩) := by
    simpa using (List.isChain_iff_getElem.mp hChain) j.val hNext
  rw [hj] at hRel
  exact hRel i rfl hNone

end StructuralRamsey.Girth
