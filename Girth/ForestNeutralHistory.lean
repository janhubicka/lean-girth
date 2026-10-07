import Girth.ForestNeutralGap
import SuccessorTree.FreeAncestralGapMap
import Mathlib.Tactic

/-!
# Removing a neutral level from a whole ancestral history

A target history of length m+k+1 is compatible with a gap at m when
its first m+1 steps end with the one code inserted by `choose`, and
every later parameter list avoids target level m. Under this condition
the history is in the image of the *actual* free one-gap shape map.

Unlike tuple-only inversion, this theorem coordinates the predecessor
history with all subsequent successor codes along one complete branch.
The multi-branch consistency required for marked B-tuples remains a
separate condition on their common meets.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

variable {Label : Type u} {arity : ℕ} [Fintype Label]

/-- A history obtained by inserting one prescribed transition at level m
and then appending only codes that do not name target level m as
an ancestor parameter. -/
inductive NeutralGapTail
    (m : ℕ)
    (choose : History Label arity m → Code Label arity m) :
    (k : ℕ) → History Label arity (m + k + 1) → Prop
  | base (h : History Label arity m) :
      NeutralGapTail m choose 0 (History.step h (choose h))
  | step {k : ℕ}
      {h : History Label arity (m + k + 1)}
      (hh : NeutralGapTail m choose k h)
      (c : Code Label arity (m + k + 1))
      (hc : ∀ j : Fin c.params.len.val, (c.params.value j).val ≠ m) :
      NeutralGapTail m choose (k + 1) (History.step h c)

/-- The one-gap map transports the deleted source code to the required
target transition, including every preserved ancestral parameter. -/
theorem gapNode_replay_deleted_code
    (m n : ℕ) (hm : m ≤ n)
    (choose : History Label arity m → Code Label arity m)
    (s : History Label arity n)
    (c : Code Label arity (n + 1))
    (hc : ∀ j : Fin c.params.len.val,
      (c.params.value j).val ≠ m) :
    let c' := deleteGapCode m n hm c hc
    gapNode m choose
        (⟨n + 1, History.step s c'⟩ : Node Label arity) =
      child
        (gapNode m choose (⟨n, s⟩ : Node Label arity))
        (gapShiftParamTuple m choose
          (⟨n, s⟩ : Node Label arity) c'.params hm)
        c.label ∧
    levelList (gapShiftParamTuple m choose
        (⟨n, s⟩ : Node Label arity) c'.params hm) =
      levelList c.params := by
  dsimp
  constructor
  · change
      gapNode m choose
          (child (⟨n, s⟩ : Node Label arity)
            (deleteGapCode m n hm c hc).params
            (deleteGapCode m n hm c hc).label) =
        child
          (gapNode m choose (⟨n, s⟩ : Node Label arity))
          (gapShiftParamTuple m choose
            (⟨n, s⟩ : Node Label arity)
            (deleteGapCode m n hm c hc).params hm)
          c.label
    exact gapNode_child_of_ge m choose
      (⟨n, s⟩ : Node Label arity)
      (deleteGapCode m n hm c hc).params c.label hm
  · calc
      levelList (gapShiftParamTuple m choose
            (⟨n, s⟩ : Node Label arity)
            (deleteGapCode m n hm c hc).params hm) =
          (levelList (deleteGapCode m n hm c hc).params).map
            (shiftNat m) :=
        levelList_gapShiftParamTuple m choose
          (⟨n, s⟩ : Node Label arity)
          (deleteGapCode m n hm c hc).params hm
      _ = levelList
            (shiftParamTuple m
              (deleteGapCode m n hm c hc).params) := by
        rw [levelList_shiftParamTuple]
      _ = levelList c.params := by
        change
          levelList
            (shiftParamTuple m
              (deleteGapParamTuple m n hm c.params hc)) =
            levelList c.params
        rw [shiftParamTuple_deleteGapParamTuple]

/-- Every compatible single-branch target history admits a shorter
ancestral history which reconstructs it under one actual global
one-gap shape map. This includes arbitrary (non-neutral) codes
above the inserted gap, provided none refers to the missing level. -/
theorem neutralGapTail_has_preimage
    (m : ℕ)
    (choose : History Label arity m → Code Label arity m) :
    ∀ {k : ℕ} {h : History Label arity (m + k + 1)},
      NeutralGapTail m choose k h →
      ∃ s : History Label arity (m + k),
        gapNode m choose
          (⟨m + k, s⟩ : Node Label arity) =
          (⟨m + k + 1, h⟩ : Node Label arity) := by
  intro k h hh
  induction hh with
  | base a =>
      refine ⟨a, ?_⟩
      simpa [child] using (gapNode_at_level m choose a)
  | @step k h hh c hc ih =>
      obtain ⟨s, hs⟩ := ih
      let n : ℕ := m + k
      let sc : Code Label arity n :=
        deleteGapCode m n (by omega) c hc
      refine ⟨History.step s sc, ?_⟩
      change
        gapNode m choose
          (child (⟨n, s⟩ : Node Label arity)
            sc.params sc.label) =
          child (⟨n + 1, h⟩ : Node Label arity)
            c.params c.label
      have hmn :
          m ≤ Node.level (⟨n, s⟩ : Node Label arity) := by
        change m ≤ n
        dsimp [n]
        omega
      rw [gapNode_child_of_ge m choose
        (⟨n, s⟩ : Node Label arity) sc.params sc.label hmn]
      rw [hs]
      congr 1
      apply levelList_injective
      have hv := (gapNode_replay_deleted_code m n
        (by omega) choose s c hc).2
      exact hv

end StructuralRamsey.Girth
