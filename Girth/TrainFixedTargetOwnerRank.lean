import Girth.TrainCyclicOwnerIsolatedNonincrease
import Mathlib.Tactic

/-!
# A conditional fixed-target lexicographic rank for owner reassignment

A chosen supreme standard i need not neighbour every designated
singleton, so one insertion can leave the cut count unchanged.
For a FIXED target i, however, replacing one non-i owner by i
strictly decreases the number of off-i positions. Combined with
checked isolated-owner cut nonincrease, the ordered pair
  (cyclic cut count, number of off-i positions)
decreases lexicographically under the finite one-position
reassignment.

This is a finite OWNER WORD lemma only. The actual long replacement
inserts TWO i-owned physical labels and changes n to n+1; its exact
owner-word transport remains open. More importantly, to use the
rank iteratively one must keep the SAME target i and transport
its supreme replacement plan. No such theorem is claimed.
No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Number of positions not owned by the distinguished target. -/
noncomputable def cyclicNonTargetCount
    (owner : Fin n → Owner) (target : Owner) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin n => owner j ≠ target)).card

/-- Changing one non-target owner to the target deletes precisely
one off-target occurrence, regardless of its neighbours. -/
theorem cyclicNonTargetCount_replace_drop
    (owner : Fin n → Owner) (k : Fin n) (target : Owner)
    (hOld : owner k ≠ target) :
    cyclicNonTargetCount (cyclicReplaceOwner owner k target) target + 1 =
      cyclicNonTargetCount owner target := by
  classical
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => owner j ≠ target)
  have hMem : k ∈ s := by
    simp [s, hOld]
  have hEq :
      (Finset.univ.filter
        (fun j : Fin n =>
          cyclicReplaceOwner owner k target j ≠ target)) =
        s.erase k := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [s, cyclicReplaceOwner]
    · simp [s, cyclicReplaceOwner, hj]
  change (Finset.univ.filter
    (fun j : Fin n =>
      cyclicReplaceOwner owner k target j ≠ target)).card + 1 =
    (Finset.univ.filter
      (fun j : Fin n => owner j ≠ target)).card
  rw [hEq]
  exact Finset.card_erase_add_one hMem

/-- The strict decrease in the second component follows directly
from the exact one-element removal identity. -/
theorem cyclicNonTargetCount_replace_lt
    (owner : Fin n → Owner) (k : Fin n) (target : Owner)
    (hOld : owner k ≠ target) :
    cyclicNonTargetCount (cyclicReplaceOwner owner k target) target <
      cyclicNonTargetCount owner target := by
  have hDrop := cyclicNonTargetCount_replace_drop owner k target hOld
  omega

/-- Under isolated singleton geometry, a fixed-target change
decreases the lexicographic rank: either cuts strictly drop, or
they stay equal and the number of off-target positions drops.
This conditional statement does NOT justify changing the target
between successive steps or silently deleting an inserted wagon. -/
theorem cyclicIsolatedOwner_fixedTarget_lex_decrease
    (hn : 2 ≤ n) (owner : Fin n → Owner)
    (k : Fin n) (target : Owner)
    (hPrev : owner (trainCyclicPred k) ≠ owner k)
    (hNext : owner k ≠ owner (cyclicSucc k))
    (hOld : owner k ≠ target) :
    (cyclicOwnerChanges (cyclicReplaceOwner owner k target) <
        cyclicOwnerChanges owner) ∨
    (cyclicOwnerChanges (cyclicReplaceOwner owner k target) =
        cyclicOwnerChanges owner ∧
      cyclicNonTargetCount (cyclicReplaceOwner owner k target) target <
        cyclicNonTargetCount owner target) := by
  have hLe := cyclicOwnerChanges_replace_isolated_le
    hn owner k target hPrev hNext
  rcases lt_or_eq_of_le hLe with hLt | hEq
  · exact Or.inl hLt
  · exact Or.inr ⟨hEq, cyclicNonTargetCount_replace_lt
      owner k target hOld⟩

end StructuralRamsey.Girth
