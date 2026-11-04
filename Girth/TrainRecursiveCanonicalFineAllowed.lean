import Girth.TrainRecursiveRefinementForget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The fine allowed sets attached to an actual first-wagon refinement

When a first-wagon refinement inserts d cuts, the lower-rank witness
needs one allowed A-part set at every fine train coordinate.

At positive inserted coordinates 1,...,d+1, use the pullback of the
ACTUAL permitted singleton of the previous refinement parent. This
includes the first retained coordinate d+1, for which the last
singleton is contained in the original first allowed set.

At subsequent retained coordinates, pull back the original allowed
set at the corresponding coarse coordinate. Level zero is unused by
the adjacent-parameter assertion and may be taken as the pullback of
the old zero allowed set.

This eliminates the formerly independent hSingleton, hFirst and
hRetained containment assumptions in the positive-cut Track B
attachment *once the fine allowed sets are chosen this way*. It
does not prove that the recursively chosen lower witness exists or
has the required positive system-girth and train certificates.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe v

variable {U P : Type v}

/-- The canonical fine allowed A-part sets for the refinement. At
positive inserted levels use its actual parent-specific permitted
sets; at all later levels use the appropriate original allowed set.
The first retained cut is deliberately treated as an inserted
parent: its last permitted singleton is controlled by the original
first allowed set. -/
def fineAllowedFromRefinement
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P)
    (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P) :
    Fin (m + d + 1) → Set U :=
  fun ρ =>
    if h : 0 < ρ.val ∧ ρ.val ≤ d + 1 then
      α ⁻¹' permitted ⟨ρ.val - 1, by omega⟩
    else
      α ⁻¹' allowed ⟨ρ.val - d, by omega⟩

/-- Each actual inserted parent has exactly its chosen permitted set,
pulled back to the source A-parts. No choice of a representative
wagon or quotienting of physical edge labels is involved. -/
theorem fineAllowedFromRefinement_parent
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (j : Fin (d + 1)) :
    fineAllowedFromRefinement m d hm α allowed permitted
      (firstRefinementParent m d hm j) = α ⁻¹' permitted j := by
  have hcase : 0 < (firstRefinementParent m d hm j).val ∧
      (firstRefinementParent m d hm j).val ≤ d + 1 := by
    change 0 < j.val + 1 ∧ j.val + 1 ≤ d + 1
    have hj := j.isLt
    omega
  simp only [fineAllowedFromRefinement, dif_pos hcase]
  have hIdx : (⟨(firstRefinementParent m d hm j).val - 1,
      by omega⟩ : Fin (d + 1)) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  rw [hIdx]

/-- Every inserted allowed A-part set is at most a singleton because
the old refinement's permitted set is, and the processed part map is
injective. -/
theorem fineAllowedFromRefinement_parent_subsingleton
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (hSingleton : ∀ j, (permitted j).Subsingleton) :
    ∀ j : Fin (d + 1),
      (fineAllowedFromRefinement m d hm α allowed permitted
        (firstRefinementParent m d hm j)).Subsingleton := by
  intro j
  rw [fineAllowedFromRefinement_parent]
  intro x hx y hy
  exact α.injective (hSingleton j hx hy)

/-- Every positive fine coordinate through d+1 uses a permitted
refinement set, and is therefore contained in the pullback of the
coarse first allowed set. -/
theorem fineAllowedFromRefinement_first_subset
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (hPermitted : ∀ j, permitted j ⊆
      allowed ⟨1, Nat.succ_lt_succ hm⟩) :
    ∀ ρ : Fin (m + d + 1),
      0 < ρ.val → ρ.val ≤ d + 1 →
      fineAllowedFromRefinement m d hm α allowed permitted ρ ⊆
        α ⁻¹' allowed ⟨1, Nat.succ_lt_succ hm⟩ := by
  intro ρ hpos hle
  have hh : 0 < ρ.val ∧ ρ.val ≤ d + 1 := ⟨hpos, hle⟩
  simp only [fineAllowedFromRefinement, dif_pos hh]
  exact Set.preimage_mono (hPermitted ⟨ρ.val - 1, by omega⟩)

/-- The first positive coarse train cut is represented by fine level
d+1, which uses the last inserted permitted singleton. -/
theorem fineAllowedFromRefinement_retained_first
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P) :
    fineAllowedFromRefinement m d hm α allowed permitted
      (EdgeTrainLevels.firstForgetIndex m d
        ⟨1, Nat.succ_lt_succ hm⟩) =
      α ⁻¹' permitted ⟨d, Nat.lt_succ_self d⟩ := by
  let j : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
  have hindex :
      EdgeTrainLevels.firstForgetIndex m d
        ⟨1, Nat.succ_lt_succ hm⟩ =
        firstRefinementParent m d hm j := by
    apply Fin.ext
    simp [EdgeTrainLevels.firstForgetIndex, firstRefinementParent, j]
  rw [hindex, fineAllowedFromRefinement_parent]

/-- Retained cuts strictly above the first one use exactly their
original allowed sets after pulling back along the processed copy. -/
theorem fineAllowedFromRefinement_retained_gt_one
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (ν : Fin (m + 1)) (hν : 1 < ν.val) :
    fineAllowedFromRefinement m d hm α allowed permitted
      (EdgeTrainLevels.firstForgetIndex m d ν) =
      α ⁻¹' allowed ν := by
  have hval : (EdgeTrainLevels.firstForgetIndex m d ν).val =
      ν.val + d := by
    simp [EdgeTrainLevels.firstForgetIndex, Nat.ne_of_gt (by omega : 0 < ν.val)]
  have hnot : ¬ (0 < (EdgeTrainLevels.firstForgetIndex m d ν).val ∧
      (EdgeTrainLevels.firstForgetIndex m d ν).val ≤ d + 1) := by
    omega
  simp only [fineAllowedFromRefinement, dif_neg hnot]
  have hIdx : (⟨(EdgeTrainLevels.firstForgetIndex m d ν).val - d,
      by omega⟩ : Fin (m + 1)) = ν := by
    apply Fin.ext
    omega
  rw [hIdx]

/-- The genuine refinement's permitted-subset field proves ALL
retained allowed-set containments, including the overlapping
first retained/last inserted parent coordinate. -/
theorem fineAllowedFromRefinement_retained_subset
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (hPermitted : ∀ j, permitted j ⊆
      allowed ⟨1, Nat.succ_lt_succ hm⟩) :
    ∀ ν : Fin (m + 1), 0 < ν.val →
      fineAllowedFromRefinement m d hm α allowed permitted
        (EdgeTrainLevels.firstForgetIndex m d ν) ⊆
      α ⁻¹' allowed ν := by
  intro ν hpos
  by_cases hone : ν.val = 1
  · have heq : ν = ⟨1, Nat.succ_lt_succ hm⟩ :=
      Fin.ext hone
    subst ν
    rw [fineAllowedFromRefinement_retained_first]
    exact Set.preimage_mono (hPermitted ⟨d, Nat.lt_succ_self d⟩)
  · have hgt : 1 < ν.val := by omega
    rw [fineAllowedFromRefinement_retained_gt_one m d hm α allowed permitted ν hgt]
    exact Set.Subset.rfl

/-- The entire fine allowed-parameter geometry required by the
larger-cutoff attachment, as a single reusable package. -/
theorem fineAllowedFromRefinement_all_constraints
    (m d : ℕ) (hm : 0 < m)
    (α : U ↪ P) (allowed : Fin (m + 1) → Set P)
    (permitted : Fin (d + 1) → Set P)
    (hPermitted : ∀ j, permitted j ⊆
      allowed ⟨1, Nat.succ_lt_succ hm⟩)
    (hSingleton : ∀ j, (permitted j).Subsingleton) :
    (∀ j : Fin (d + 1),
      (fineAllowedFromRefinement m d hm α allowed permitted
        (firstRefinementParent m d hm j)).Subsingleton) ∧
    (∀ ρ : Fin (m + d + 1), 0 < ρ.val → ρ.val ≤ d + 1 →
      fineAllowedFromRefinement m d hm α allowed permitted ρ ⊆
        α ⁻¹' allowed ⟨1, Nat.succ_lt_succ hm⟩) ∧
    (∀ ν : Fin (m + 1), 0 < ν.val →
      fineAllowedFromRefinement m d hm α allowed permitted
        (EdgeTrainLevels.firstForgetIndex m d ν) ⊆
        α ⁻¹' allowed ν) := by
  exact ⟨fineAllowedFromRefinement_parent_subsingleton m d hm α allowed
    permitted hSingleton,
    fineAllowedFromRefinement_first_subset m d hm α allowed
      permitted hPermitted,
    fineAllowedFromRefinement_retained_subset m d hm α allowed
      permitted hPermitted⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
