import Girth.ForestMeetGuardGap
import Girth.ForestGuardedSkeletonBound
import Mathlib.Tactic

/-!
# Meet-skeleton membership gives the exact simultaneous gap guard

The guarded marked-diary skeleton already marks terminal levels and
every pairwise meet of the q selected free-ancestral histories.
Consequently a level *omitted* from that skeleton cannot be a meet
at which selected branches choose different inserted successor codes.

Together with locally checked neutral tails, this supplies ONE global
admissible one-gap shape map for all q histories. This converts the
previous purely cardinality-based skeleton into a constructive
syntactic neutral-deletion tool.

It does not show that the actual train's raw predecessor parameters
avoid omitted skeleton levels: that genuinely geometric recoding input
remains missing.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

/-- Each pairwise meet level is explicitly present in the finite
terminal-and-meet skeleton, including repeated leaves. -/
theorem forestTerminalMeetLevels_contains_meet
    {Label : Type u} [Fintype Label] {arity : ℕ}
    (q : ℕ) (leaves : Fin q → Node Label arity)
    (i j : Fin q) :
    LevelTree.lev (LevelTree.meet (leaves i) (leaves j)) ∈
      forestTerminalMeetLevels q leaves := by
  classical
  unfold forestTerminalMeetLevels
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  refine ⟨(i, j), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- Omitting m from the skeleton excludes it from EVERY selected
pairwise meet, not just pairs with equal preceding stems. -/
theorem forestTerminalMeetLevels_unmarked_not_meet
    {Label : Type u} [Fintype Label] {arity : ℕ}
    (q : ℕ) (leaves : Fin q → Node Label arity) (m : ℕ)
    (hm : m ∉ forestTerminalMeetLevels q leaves)
    (i j : Fin q) :
    (meetNode (leaves i) (leaves j)).level ≠ m := by
  intro hEq
  have hMem := forestTerminalMeetLevels_contains_meet q leaves i j
  change (meetNode (leaves i) (leaves j)).level ∈
    forestTerminalMeetLevels q leaves at hMem
  rw [hEq] at hMem
  exact hm hMem

/-- A locally neutral gap outside the actual finite pairwise meet
skeleton always has common global one-gap preimages. -/
theorem finiteLocalNeutralGap_preimages_of_skeleton
    {Label : Type u} {arity : ℕ}
    [Fintype Label] [Nonempty Label]
    (m k q : ℕ)
    (stem : Fin q → History Label arity m)
    (code : Fin q → Code Label arity m)
    (target : Fin q → History Label arity (m + k + 1))
    (hLocal : ∀ i : Fin q,
      LocalNeutralGapTail m (stem i) (code i) k (target i))
    (hNotMeet : m ∉
      forestTerminalMeetLevels q
        (fun i => (⟨m + k + 1, target i⟩ : Node Label arity))) :
    ∃ choose : History Label arity m → Code Label arity m,
      ∃ source : Fin q → History Label arity (m + k),
        ∀ i : Fin q,
          gapNode m choose
            (⟨m + k, source i⟩ : Node Label arity) =
            (⟨m + k + 1, target i⟩ : Node Label arity) := by
  apply finiteLocalNeutralGap_preimages_of_unmarkedMeets
    m k q stem code target hLocal
  intro i j _
  exact forestTerminalMeetLevels_unmarked_not_meet q
    (fun i => (⟨m + k + 1, target i⟩ : Node Label arity))
    m hNotMeet i j

/-- The stronger full diary skeleton also includes the terminal/meet
set. Thus every omitted level, subject only to actual neutral local
successor codes, admits one simultaneous free-ancestral gap map. -/
theorem finiteLocalNeutralGap_preimages_of_diarySkeleton
    {Label : Type u} {arity : ℕ}
    [Fintype Label] [Nonempty Label]
    (m k q : ℕ)
    (stem : Fin q → History Label arity m)
    (code : Fin q → Code Label arity m)
    (target : Fin q → History Label arity (m + k + 1))
    (active : Finset ℕ)
    (hLocal : ∀ i : Fin q,
      LocalNeutralGapTail m (stem i) (code i) k (target i))
    (hNotMarked : m ∉
      forestDiarySkeleton active
        (forestTerminalMeetLevels q
          (fun i => (⟨m + k + 1, target i⟩ : Node Label arity)))) :
    ∃ choose : History Label arity m → Code Label arity m,
      ∃ source : Fin q → History Label arity (m + k),
        ∀ i : Fin q,
          gapNode m choose
            (⟨m + k, source i⟩ : Node Label arity) =
            (⟨m + k + 1, target i⟩ : Node Label arity) := by
  have hNotMeet : m ∉ forestTerminalMeetLevels q
      (fun i => (⟨m + k + 1, target i⟩ : Node Label arity)) := by
    intro hMeet
    apply hNotMarked
    unfold forestDiarySkeleton
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    right
    exact hMeet
  exact finiteLocalNeutralGap_preimages_of_skeleton
    m k q stem code target hLocal hNotMeet

end StructuralRamsey.Girth
