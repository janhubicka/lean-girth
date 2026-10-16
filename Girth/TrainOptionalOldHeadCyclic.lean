import Girth.TrainOptionalOldCyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-!
# Circulation: one successor rule for all retained connectors

The successor of the original connector at i is always the FIRST
connector of the next source block, whether that block begins with a
fresh insertion or directly with its old connector. The same statement
includes the cyclic wrap. A single rule therefore handles both the
no-insertion A3 argument and the fresh-wagon predecessor required in A2.

This module proves a pure list theorem, without output BigCycle,
output A2/A3, geometric wagon hypotheses, or appendix lemmas.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- First connector in a block, inserted when present, old otherwise. -/
def optionalConnectorHead
    (base : Fin n → α) (insert : Fin n → Option α)
    (i : Fin n) : α :=
  (insert i).getD (base i)

theorem optionalConnectorBlock_head?_eq
    (base : Fin n → α) (insert : Fin n → Option α)
    (i : Fin n) :
    (optionalConnectorBlock base insert i).head? =
      some (optionalConnectorHead base insert i) := by
  cases hi : insert i with
  | none => simp [optionalConnectorBlock, optionalConnectorHead, hi]
  | some a => simp [optionalConnectorBlock, optionalConnectorHead, hi]

/-- Ordinary adjacency relation for old-to-next-block connectors. -/
def optionalOldHeadFollows
    (base : Fin n → α) (insert : Fin n → Option α)
    (a b : α) : Prop :=
  ∀ i : Fin n, a = base i →
    b = optionalConnectorHead base insert (cyclicSucc i)

/-- Every adjacent pair in the flattened word satisfies this relation
except the last-to-first wrap, treated below. -/
theorem optionalConnectorWord_oldHead_chain
    (base : Fin n → α) (insert : Fin n → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j) :
    (optionalConnectorWord base insert).IsChain
      (optionalOldHeadFollows base insert) := by
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
            optionalOldHeadFollows base insert fresh (base i) := by
          intro j hj
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
          optionalOldHeadFollows base insert a b := by
      intro a ha b hb k hak
      have haEq : a = base i := by
        have h : base i = a := by
          simpa [optionalConnectorBlock_last?] using ha
        exact h.symm
      have hki : k = i := hBase (hak.symm.trans haEq)
      have hbEq : b = optionalConnectorHead base insert j := by
        exact Option.some.inj
          (hb.symm.trans (optionalConnectorBlock_head?_eq base insert j))
      simpa [hki, hSucc] using hbEq
    simpa [List.get_ofFn, i, j] using hBoundary

theorem optionalConnectorWord_old_head_of_nonlast
    (base : Fin n → α) (insert : Fin n → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j)
    (i : Fin n)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = base i)
    (hNext : j.val + 1 < (optionalConnectorWord base insert).length) :
    (optionalConnectorWord base insert).get
      ⟨j.val + 1, hNext⟩ =
      optionalConnectorHead base insert (cyclicSucc i) := by
  have hChain :=
    optionalConnectorWord_oldHead_chain base insert hBase hFresh
  have hRel : optionalOldHeadFollows base insert
      ((optionalConnectorWord base insert).get j)
      ((optionalConnectorWord base insert).get ⟨j.val + 1, hNext⟩) := by
    simpa using (List.isChain_iff_getElem.mp hChain) j.val hNext
  rw [hj] at hRel
  exact hRel i rfl

theorem optionalConnectorWord_head?_eq_firstHead
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α) :
    (optionalConnectorWord base insert).head? =
      some (optionalConnectorHead base insert 0) := by
  unfold optionalConnectorWord
  rw [List.ofFn_succ]
  cases h0 : insert 0 with
  | none => simp [optionalConnectorBlock, optionalConnectorHead, h0]
  | some fresh => simp [optionalConnectorBlock, optionalConnectorHead, h0]

/-- Uniform cyclic successor: old_i is followed by the next block head,
which is the fresh insertion if any, otherwise old_(i+1). -/
theorem optionalConnectorWord_old_cyclic_head
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin (n + 1)) (a : α),
      insert i = some a → a ≠ base j)
    (i : Fin (n + 1))
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = base i) :
    (optionalConnectorWord base insert).get (cyclicSucc j) =
      optionalConnectorHead base insert (cyclicSucc i) := by
  let word := optionalConnectorWord base insert
  by_cases hNext : j.val + 1 < word.length
  · have hSucc : cyclicSucc j = ⟨j.val + 1, hNext⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hNext
    rw [hSucc]
    exact optionalConnectorWord_old_head_of_nonlast
      base insert hBase hFresh i j hj hNext
  · have hjLt : j.val < word.length := by
      simpa [word] using j.isLt
    have hLastPos : word.length - 1 = j.val := by omega
    have hGetLast : word.getLast? = some (word.get j) := by
      rw [List.getLast?_eq_getElem?, hLastPos]
      exact List.getElem?_eq_getElem j.isLt
    have hLast : word.getLast? = some (base (Fin.last n)) :=
      optionalConnectorWord_getLast?_succ base insert
    have hiLast : i = Fin.last n := by
      apply hBase
      exact Option.some.inj
        ((hGetLast.trans (congrArg some hj)).symm.trans hLast)
    have hSourceWrap :
        cyclicSucc (Fin.last n) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      change (n + 1) % (n + 1) = 0
      exact Nat.mod_self _
    have hFirst :
        word.head? = some (optionalConnectorHead base insert 0) :=
      optionalConnectorWord_head?_eq_firstHead base insert
    have hLenPos : 0 < word.length := by omega
    have hAtFirst :
        word.get ⟨0, hLenPos⟩ =
          optionalConnectorHead base insert 0 := by
      have hGetHead :
          word.head? = some (word.get ⟨0, hLenPos⟩) := by
        rw [List.head?_eq_getElem?]
        exact List.getElem?_eq_getElem hLenPos
      exact Option.some.inj (hGetHead.symm.trans hFirst)
    have hOutWrap : cyclicSucc j = ⟨0, hLenPos⟩ := by
      apply Fin.ext
      change (j.val + 1) % word.length = 0
      have hEq : j.val + 1 = word.length := by omega
      rw [hEq, Nat.mod_self]
    rw [hOutWrap, hiLast, hSourceWrap]
    exact hAtFirst

end StructuralRamsey.Girth
