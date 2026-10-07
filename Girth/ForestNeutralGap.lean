import Girth.ForestDiarySpine
import SuccessorTree.FreeAncestralGap
import Mathlib.Tactic

/-!
# Removing a neutral gap from ancestral parameter codes

For a one-gap shape map skipping target level m, every ancestral
parameter index is shifted by `shiftFin m n`; the skipped level m is
never hit. Conversely, for m ≤ n every target parameter tuple that
avoids level m admits a unique preimage tuple. This is the code-level
inverse needed when deleting a neutral unmarked level from a guarded
forest diary.

This is NOT yet the inverse theorem for an entire q-marked history
subtree; that theorem additionally coordinates neutral successor
choices at branching nodes.
-/

namespace StructuralRamsey.Girth

open SuccessorTree.FreeAncestral

/-- Shifted parameters never land at the newly inserted gap. -/
theorem shiftedParamLevel_ne_gap
    (m n : ℕ) (i : Fin n) :
    (shiftFin m n i).val ≠ m := by
  by_cases hi : i.val < m
  · rw [shiftFin_val_of_lt i hi]
    omega
  · rw [shiftFin_val_of_ge i (by omega : m ≤ i.val)]
    omega

/-- Numerical inverse to the gap insertion, defined when the target
parameter avoids the inserted level. -/
def deleteGapFin (m n : ℕ) (hm : m ≤ n)
    (i : Fin (n + 1)) (hi : i.val ≠ m) : Fin n :=
  if h : i.val < m then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by omega⟩

theorem shiftFin_deleteGapFin
    (m n : ℕ) (hm : m ≤ n)
    (i : Fin (n + 1)) (hi : i.val ≠ m) :
    shiftFin m n (deleteGapFin m n hm i hi) = i := by
  apply Fin.ext
  by_cases h : i.val < m
  · have hval :
        (deleteGapFin m n hm i hi).val = i.val := by
      simp [deleteGapFin, h]
    rw [shiftFin_val_of_lt (deleteGapFin m n hm i hi) (by omega)]
    exact hval
  · have him : m < i.val := by omega
    have hval :
        (deleteGapFin m n hm i hi).val = i.val - 1 := by
      simp [deleteGapFin, h]
    rw [shiftFin_val_of_ge
      (deleteGapFin m n hm i hi) (by omega : m ≤ (deleteGapFin m n hm i hi).val)]
    omega

theorem deleteGapFin_shiftFin
    (m n : ℕ) (hm : m ≤ n) (i : Fin n) :
    deleteGapFin m n hm
      (shiftFin m n i) (shiftedParamLevel_ne_gap m n i) = i := by
  apply Fin.ext
  by_cases h : i.val < m
  · have hs := shiftFin_val_of_lt i h
    have hval :
        (deleteGapFin m n hm
          (shiftFin m n i) (shiftedParamLevel_ne_gap m n i)).val =
          (shiftFin m n i).val := by
      simp [deleteGapFin, hs, h]
    omega
  · have hs := shiftFin_val_of_ge i (by omega : m ≤ i.val)
    have hval :
        (deleteGapFin m n hm
          (shiftFin m n i) (shiftedParamLevel_ne_gap m n i)).val =
          (shiftFin m n i).val - 1 := by
      simp [deleteGapFin, hs, show ¬i.val + 1 < m by omega]
    omega

/-- Delete level m from an entire bounded tuple when no parameter
references that level. -/
def deleteGapParamTuple {arity : ℕ}
    (m n : ℕ) (hm : m ≤ n)
    (t : ParamTuple arity (n + 1))
    (ht : ∀ j : Fin t.len.val, (t.value j).val ≠ m) :
    ParamTuple arity n where
  len := t.len
  value := fun j => deleteGapFin m n hm (t.value j) (ht j)

/-- Inserting the deleted gap reconstructs the original tuple. -/
theorem shiftParamTuple_deleteGapParamTuple {arity : ℕ}
    (m n : ℕ) (hm : m ≤ n)
    (t : ParamTuple arity (n + 1))
    (ht : ∀ j : Fin t.len.val, (t.value j).val ≠ m) :
    shiftParamTuple m (deleteGapParamTuple m n hm t ht) = t := by
  apply levelList_injective
  simp only [levelList_shiftParamTuple, levelList,
    deleteGapParamTuple, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change shiftNat m
      (deleteGapFin m n hm (t.value j) (ht j)).val =
    (t.value j).val
  have h :=
    congrArg Fin.val
      (shiftFin_deleteGapFin m n hm (t.value j) (ht j))
  have hval :
      shiftNat m
        (deleteGapFin m n hm (t.value j) (ht j)).val =
      (shiftFin m n
        (deleteGapFin m n hm (t.value j) (ht j))).val := by
    by_cases hx :
      (deleteGapFin m n hm (t.value j) (ht j)).val < m
    · simp [shiftNat, shiftFin, hx]
    · simp [shiftNat, shiftFin, hx]
  exact hval.trans h

/-- Removing a neutral level also transports the transition label
unchanged, not just its ancestral parameter indices. -/
def deleteGapCode {Label : Type*} {arity : ℕ}
    (m n : ℕ) (hm : m ≤ n)
    (c : Code Label arity (n + 1))
    (hc : ∀ j : Fin c.params.len.val,
      (c.params.value j).val ≠ m) :
    Code Label arity n :=
  ⟨c.label, deleteGapParamTuple m n hm c.params hc⟩

theorem shiftCode_deleteGapCode {Label : Type*} {arity : ℕ}
    (m n : ℕ) (hm : m ≤ n)
    (c : Code Label arity (n + 1))
    (hc : ∀ j : Fin c.params.len.val,
      (c.params.value j).val ≠ m) :
    shiftCode m (deleteGapCode m n hm c hc) = c := by
  rcases c with ⟨label, params⟩
  change
    Code.mk label
      (shiftParamTuple m
        (deleteGapParamTuple m n hm params hc)) =
      Code.mk label params
  exact congrArg (Code.mk label)
    (shiftParamTuple_deleteGapParamTuple m n hm params hc)

end StructuralRamsey.Girth
