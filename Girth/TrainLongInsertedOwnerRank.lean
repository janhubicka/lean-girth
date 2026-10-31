import Mathlib.Tactic

/-!
# Fixed-target rank during a literal one-long (n -> n+1) insertion

The simultaneous-replacement module inserts TWO consecutive physical
edge labels in place of one original owner occurrence when the long
piece is sourced from a chosen standard i. Once the output owner
assignment is shown to consist of the same prefix and suffix and two
i-owned entries, the off-i count drops by EXACTLY one.

Unlike the older fixed-length owner-reassignment lemma, this is
a genuine LENGTH-INCREASING list identity. It does not identify the
source/output Fin indices, prove owner admissibility for actual
selected-picture edge labels, or transport a fixed supreme plan.
These remain the substantive Path A tasks. Circulation only.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v}

/-- Number of entries of a finite owner word which do not equal the
fixed distinguished target. The implementation is classical, so it
works even when the owner type is infinite. -/
noncomputable def listNonTargetCount (xs : List Owner) (target : Owner) : ℕ := by
  classical
  exact (xs.filter (fun x => x ≠ target)).length

/-- Replacing any non-target entry by TWO successive target entries
reduces the off-target count by exactly one, independent of position,
original number of cuts, or whether the target occurred elsewhere. -/
theorem listNonTargetCount_insert_two_target
    (before after : List Owner) (old target : Owner)
    (hOld : old ≠ target) :
    listNonTargetCount (before ++ target :: target :: after) target + 1 =
      listNonTargetCount (before ++ old :: after) target := by
  classical
  simp [listNonTargetCount, List.filter_append, hOld]

/-- Hence the second component of a fixed-target rank is strictly
smaller after insertion. This does NOT imply the first (cut) component
strictly decreases. -/
theorem listNonTargetCount_insert_two_target_lt
    (before after : List Owner) (old target : Owner)
    (hOld : old ≠ target) :
    listNonTargetCount (before ++ target :: target :: after) target <
      listNonTargetCount (before ++ old :: after) target := by
  have hDrop := listNonTargetCount_insert_two_target
    before after old target hOld
  omega

end StructuralRamsey.Girth
