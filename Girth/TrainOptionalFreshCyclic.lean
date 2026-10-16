import Girth.TrainOptionalFreshSuccessor
import Mathlib.Tactic

/-!
# Circulation: the cyclic successor of an inserted fresh wagon

In the literal optional-insertion connector word each source connector is
retained at the END of its block.  Consequently the LAST connector of
the complete nonempty word is always an original source connector,
never a fresh inserted wagon.

Together with the previously checked fresh-to-old ordinary list chain,
this eliminates the last-position exception: every inserted token has
a cyclic successor, and it is exactly its original source connector.

The result is a reusable generic Fin/List lemma. It does not assume an
output BigCycle, acceptability or wagon linearity. The next application
will identify actual B.connector (cyclicSucc j) with an oldPos connector.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- The final connector of a nonempty optional insertion word is the
original connector of the last source block. -/
theorem optionalConnectorWord_getLast?_succ
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α) :
    (optionalConnectorWord base insert).getLast? =
      some (base (Fin.last n)) := by
  unfold optionalConnectorWord
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, List.flatten_append]
  cases hi : insert (Fin.last n) with
  | none => simp [optionalConnectorBlock, hi]
  | some a => simp [optionalConnectorBlock, hi]

/-- The position of a fresh token is NEVER the last physical position.
Here freshness relative to the old connectors is essential. -/
theorem optionalConnectorWord_fresh_not_last
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α)
    (hFresh : ∀ (i j : Fin (n + 1)) (a : α),
      insert i = some a → a ≠ base j)
    (i : Fin (n + 1)) (a : α) (hi : insert i = some a)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = a) :
    j.val + 1 < (optionalConnectorWord base insert).length := by
  classical
  let word := optionalConnectorWord base insert
  by_contra hLast
  have hPos : word.length - 1 = j.val := by
    dsimp [word] at hLast
    omega
  have hGetLast : word.getLast? = some a := by
    rw [List.getLast?_eq_getElem?, hPos]
    simpa [List.getElem?_eq_getElem] using congrArg some hj
  have hActualLast : word.getLast? = some (base (Fin.last n)) :=
    optionalConnectorWord_getLast?_succ base insert
  have hEq : a = base (Fin.last n) :=
    Option.some.inj (hGetLast.symm.trans hActualLast)
  exact (hFresh i (Fin.last n) a hi) hEq

/-- The CYCLIC successor of every genuinely fresh connector is exactly
its old source right connector, including the potential wrap case
(which cannot actually occur for a fresh token). -/
theorem optionalConnectorWord_fresh_cyclic_successor
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α)
    (hFresh : ∀ (i j : Fin (n + 1)) (a : α),
      insert i = some a → a ≠ base j)
    (hDifferent : ∀ (i j : Fin (n + 1)) (a b : α),
      i ≠ j → insert i = some a → insert j = some b → a ≠ b)
    (i : Fin (n + 1)) (a : α) (hi : insert i = some a)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = a) :
    (optionalConnectorWord base insert).get (cyclicSucc j) = base i := by
  have hNext := optionalConnectorWord_fresh_not_last
    base insert hFresh i a hi j hj
  have hSucc : cyclicSucc j = ⟨j.val + 1, hNext⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hNext
  rw [hSucc]
  exact optionalConnectorWord_fresh_successor_of_nonlast
    base insert hFresh hDifferent i a hi j hj hNext

end StructuralRamsey.Girth
