import Girth.ForestObservableEventBound
import Girth.ForestDiarySpine
import SuccessorTree.FreeAncestralLevelTree
import Mathlib.Tactic

/-!
# Uniform marked level skeleton from observable train changes

The observable record-change bound combines with the elementary
terminal-and-meet bound for a fixed q-family of free ancestral histories:
there are at most q terminal levels and q² ordered-pair meet levels.
Mark also the bases/precedessors of every record-changing active step.
The resulting level skeleton has uniformly bounded cardinality.

This is a cardinality statement. It does not prove that the actual
partite/train history's necessary parameter levels are among these
marks, or that omitted levels can be assigned neutral empty-parameter
codes; those are the remaining geometric diary normalisation
requirements.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

/-- Levels of all marked terminal histories and all pairwise meets.
The ordered-pair formulation also handles repeated selected leaves. -/
noncomputable def forestTerminalMeetLevels
    {Label : Type u} [Fintype Label] {arity : ℕ}
    (q : ℕ) (leaves : Fin q → Node Label arity) :
    Finset ℕ :=
  let I : Finset (Fin q) := Finset.univ
  (I.image (fun i => LevelTree.lev (leaves i))) ∪
    ((I.product I).image
      (fun p => LevelTree.lev
        (LevelTree.meet (leaves p.1) (leaves p.2))))

/-- A q-tuple has at most q distinct terminal levels and q² ordered
pairwise meet levels, with no assumption on the ambient history depth. -/
theorem forestTerminalMeetLevels_card_le
    {Label : Type u} [Fintype Label] {arity : ℕ}
    (q : ℕ) (leaves : Fin q → Node Label arity) :
    (forestTerminalMeetLevels q leaves).card ≤ q + q * q := by
  classical
  let I : Finset (Fin q) := Finset.univ
  have ht :
      (I.image (fun i => LevelTree.lev (leaves i))).card ≤ q := by
    calc
      (I.image (fun i => LevelTree.lev (leaves i))).card ≤
          I.card := Finset.card_image_le
      _ = q := by simp [I]
  have hm :
      ((I.product I).image
          (fun p => LevelTree.lev
            (LevelTree.meet (leaves p.1) (leaves p.2)))).card ≤
        q * q := by
    calc
      ((I.product I).image
          (fun p => LevelTree.lev
            (LevelTree.meet (leaves p.1) (leaves p.2)))).card ≤
          (I.product I).card := Finset.card_image_le
      _ = q * q := by simp [I]
  have hUnion :
      ((I.image (fun i => LevelTree.lev (leaves i))) ∪
        ((I.product I).image
          (fun p => LevelTree.lev
            (LevelTree.meet (leaves p.1) (leaves p.2))))).card ≤
      (I.image (fun i => LevelTree.lev (leaves i))).card +
      ((I.product I).image
          (fun p => LevelTree.lev
            (LevelTree.meet (leaves p.1) (leaves p.2)))).card :=
    Finset.card_union_le _ _
  change
    ((I.image (fun i => LevelTree.lev (leaves i))) ∪
      ((I.product I).image
        (fun p => LevelTree.lev
          (LevelTree.meet (leaves p.1) (leaves p.2))))).card ≤
      q + q * q
  omega

/-- Conditional explicit diary-level bound: if every *selected*
active stage adds a new observable equality/edge-birth record, the
level set retaining those stages, their immediate predecessors and
all marked terminal/meet levels is bounded independently of the
length of the history construction. -/
theorem forestObservableDiarySkeleton_card_le
    {Label : Type u} [Fintype Label] {arity : ℕ}
    (q v e N : ℕ)
    (leaves : Fin q → Node Label arity)
    (R : ℕ → Finset (ForestObservableAtom q v e))
    (active : ℕ → Prop) [DecidablePred active]
    (hMono : ∀ i : ℕ, i < N → R i ⊆ R (i + 1))
    (hActive :
      ∀ i : ℕ, i < N → active i → R i ⊂ R (i + 1)) :
    (forestDiarySkeleton ((Finset.range N).filter active)
        (forestTerminalMeetLevels q leaves)).card ≤
      1 + 2 * ((q * v) * (q * v) + q * e) +
        q + q * q := by
  have ha := markedObservableEvent_bound q v e R active N
    hMono hActive
  have hm := forestTerminalMeetLevels_card_le q leaves
  have hb := forestDiarySkeleton_card_le
    ((Finset.range N).filter active)
    (forestTerminalMeetLevels q leaves)
  omega

end StructuralRamsey.Girth
