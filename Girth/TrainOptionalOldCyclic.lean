import Girth.TrainOptionalOldSuccessor
import Girth.TrainOptionalFreshCyclic
import Mathlib.Tactic

/-!
# Circulation: old connector successors at the cyclic wrap

The checked ordinary old-connector successor chain says: if no fresh
wagon is inserted before the NEXT source block, then an old connector
is followed by the next old connector, away from the final list index.

The final list connector is ALWAYS the last old source connector.
Thus the only missing case is its cyclic wrap to the first block.
If the first source block has no insertion, its first token is
precisely base 0. This proves the SAME successor relation even at the
last output position.

This is the generic list-side equation required to prove inherited
output-wagon neighbour positions and reduce physical output A3 to
the checked conditional transfer. It does not infer output A2/A3,
linearity, or an output BigCycle from the list alone.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- With no insertion at the first source block, the actual literal
connector list begins with the first original source connector. -/
theorem optionalConnectorWord_head?_of_none_zero
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α)
    (h0 : insert 0 = none) :
    (optionalConnectorWord base insert).head? = some (base 0) := by
  unfold optionalConnectorWord
  rw [List.ofFn_succ]
  simp [optionalConnectorBlock, h0]

/-- A source connector whose NEXT source block has no inserted token
has exactly its old successor even in the CIRCULAR output word.

The proof uses the nonwrap List.IsChain theorem for ordinary indices;
the last index is handled by the fact that the last token is old and
that the first token is base 0 when the cyclic first block has none. -/
theorem optionalConnectorWord_old_cyclic_successor
    (base : Fin (n + 1) → α)
    (insert : Fin (n + 1) → Option α)
    (hBase : Function.Injective base)
    (hFresh : ∀ (i j : Fin (n + 1)) (a : α),
      insert i = some a → a ≠ base j)
    (i : Fin (n + 1))
    (hNone : insert (cyclicSucc i) = none)
    (j : Fin (optionalConnectorWord base insert).length)
    (hj : (optionalConnectorWord base insert).get j = base i) :
    (optionalConnectorWord base insert).get (cyclicSucc j) =
      base (cyclicSucc i) := by
  let word := optionalConnectorWord base insert
  by_cases hNext : j.val + 1 < word.length
  · have hSucc : cyclicSucc j = ⟨j.val + 1, hNext⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hNext
    rw [hSucc]
    exact optionalConnectorWord_old_successor_of_nonlast
      base insert hBase hFresh i hNone j hj hNext
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
    have hNone0 : insert (0 : Fin (n + 1)) = none := by
      rw [hiLast, hSourceWrap] at hNone
      exact hNone
    have hFirst? :
        word.head? = some (base (0 : Fin (n + 1))) :=
      optionalConnectorWord_head?_of_none_zero base insert hNone0
    have hLenPos : 0 < word.length := by omega
    have hFirst : word.get ⟨0, hLenPos⟩ = base (0 : Fin (n + 1)) := by
      have hGetHead :
          word.head? = some (word.get ⟨0, hLenPos⟩) := by
        rw [List.head?_eq_getElem?]
        exact List.getElem?_eq_getElem hLenPos
      exact Option.some.inj (hGetHead.symm.trans hFirst?)
    have hOutWrap : cyclicSucc j = ⟨0, hLenPos⟩ := by
      apply Fin.ext
      change (j.val + 1) % word.length = 0
      have hEq : j.val + 1 = word.length := by omega
      rw [hEq, Nat.mod_self]
    rw [hOutWrap, hiLast, hSourceWrap]
    exact hFirst

end StructuralRamsey.Girth
