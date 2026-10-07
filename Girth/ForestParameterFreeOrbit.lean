import Girth.ForestSuccessorBridge
import SuccessorTree.FreeAncestralMonoid
import SuccessorTree.FreeAncestralGapShape
import SuccessorTree.ShapeEvents
import Mathlib.Tactic

/-!
# Root-moving free shapes and parameter-free event orbits

In the free ancestral history SMTree, one-gap maps may insert any desired
intrinsic code before the image of the source root. Repeated insertions
move the root to any selected history prefix. Consequently every legal
parameter-free event of one fixed label is a transported instance of
the same canonical root event.

This proves only a SYNTACTIC support-role normalization. It remains to
show that actual A-atom occurrences in the girth picture can all be
given such parameter-free roles with a faithful geometric evaluation.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u

variable {Label : Type u} {arity : ℕ}
variable [Fintype Label] [Nonempty Label]

/-- A free one-gap map can target one prescribed child code and insert
a neutral empty-parameter code over all other nodes on that level. -/
noncomputable def rootPrefixChoice
    (n : ℕ) (h : History Label arity n)
    (c : Code Label arity n) :
    History Label arity n → Code Label arity n := by
  classical
  exact fun t => if t = h then c else
    ⟨defaultLabel, emptyParamTuple arity n⟩

@[simp] theorem rootPrefixChoice_self
    (n : ℕ) (h : History Label arity n)
    (c : Code Label arity n) :
    rootPrefixChoice n h c h = c := by
  classical
  simp [rootPrefixChoice]

/-- Every finite free history is the image of the root under a global
shape-preserving map: insert its codes successively before the root image. -/
theorem exists_free_shape_from_root :
    ∀ (n : ℕ) (h : History Label arity n),
      ∃ F : ShapeMap
          (freeSTree (Label := Label) (arity := arity)),
        F (rootNode (Label := Label) (arity := arity)) =
          (⟨n, h⟩ : Node Label arity) := by
  intro n
  induction n with
  | zero =>
      intro h
      have hh : h = History.root := history_zero_unique h
      subst h
      exact ⟨ShapeMap.id freeSTree, rfl⟩
  | succ n ih =>
      intro h
      cases h with
      | step parent code =>
          obtain ⟨F, hF⟩ := ih parent
          let choose :=
            rootPrefixChoice (arity := arity) n parent code
          let D : ShapeMap
              (freeSTree (Label := Label) (arity := arity)) :=
            oneGapShapeMap n choose
          refine ⟨D.comp F, ?_⟩
          change D (F (rootNode (Label := Label) (arity := arity))) =
            (⟨n + 1, History.step parent code⟩ : Node Label arity)
          rw [hF]
          change oneGapShapeMap n choose
              (⟨n, parent⟩ : Node Label arity) =
            (⟨n + 1, History.step parent code⟩ : Node Label arity)
          rw [oneGapShapeMap_apply, gapNode_at_level]
          simp [choose, rootPrefixChoice, child]

/-- A one-step intrinsic event at the formal root, with empty parameters. -/
noncomputable def canonicalEmptyEvent (c : Label) :
    IntrinsicEvent
      (freeSTree (Label := Label) (arity := arity)) where
  base := rootNode
  params := []
  label := c
  has_child := by
    refine
      ⟨child (rootNode (Label := Label) (arity := arity))
        (emptyParamTuple arity 0) c, ?_⟩
    have hs :=
      freeSucc_paramNodes
        (rootNode (Label := Label) (arity := arity))
        (emptyParamTuple arity 0) c
    simpa [rootNode, paramNodes, emptyParamTuple] using hs

/-- All parameter-free events with one label are reachable from the
canonical root event in the corresponding three intrinsic fields.
Geometric support-atom identification remains a separate hypothesis. -/
theorem parameterFreeEvent_rootOrbit
    (a : Node Label arity) (c : Label) :
    ∃ F : ShapeMap
        (freeSTree (Label := Label) (arity := arity)),
      (F.mapEvent (canonicalEmptyEvent (arity := arity) c)).base = a ∧
      (F.mapEvent (canonicalEmptyEvent (arity := arity) c)).params = [] ∧
      (F.mapEvent (canonicalEmptyEvent (arity := arity) c)).label = c := by
  rcases a with ⟨n, h⟩
  obtain ⟨F, hF⟩ :=
    exists_free_shape_from_root (arity := arity) n h
  refine ⟨F, ?_, ?_, ?_⟩
  · exact hF
  · rfl
  · rfl

end StructuralRamsey.Girth
