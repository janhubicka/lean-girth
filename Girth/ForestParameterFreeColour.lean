import Girth.ForestRootColourCanon
import SuccessorTree.ShapeEvents

/-!
# Finite Ramsey canonisation of parameter-free intrinsic event colours

The generic root-orbit Ramsey result applies to intrinsic successor
events whose ancestral parameter list is empty and whose label is
fixed. Every such event is determined by its birth base, so the
finite Ramsey result makes all its images under a single shape
reduction monochromatic.

This says nothing about whether actual support A-atoms of a girth
picture can be coded with empty-parameter births, or whether their
geometric images are faithful under the reduction.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u v

variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- The parameter-free occurrence of label c at an arbitrary
ancestral history node. -/
noncomputable def emptyEventAtNode
    (arity : ℕ) (a : Node Label arity) (c : Label) :
    IntrinsicEvent (freeSTree (Label := Label) (arity := arity)) where
  base := a
  params := []
  label := c
  has_child := by
    refine ⟨child a (emptyParamTuple arity a.level) c, ?_⟩
    change freeSucc a [] c =
      some (child a (emptyParamTuple arity a.level) c)
    have hs := freeSucc_paramNodes a
      (emptyParamTuple arity a.level) c
    simpa [paramNodes, emptyParamTuple] using hs

/-- Transporting a parameter-free intrinsic event is exactly
transporting its base node; no extra ancestral support parameter
must be respected. -/
@[simp] theorem map_emptyEventAtNode
    (arity : ℕ)
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (a : Node Label arity) (c : Label) :
    F.mapEvent (emptyEventAtNode arity a c) =
      emptyEventAtNode arity (F a) c := rfl

/-- The root event from the existing orbit theorem has this
uniform parameter-free representation. -/
theorem canonicalEmptyEvent_eq_emptyEventAtNode
    (arity : ℕ) (c : Label) :
    canonicalEmptyEvent (arity := arity) c =
      emptyEventAtNode arity
        (rootNode (Label := Label) (arity := arity)) c := rfl

/-- All images of the fixed-label, parameter-free birth role are
monochromatic after one finite-dimensional free shape reduction. -/
theorem parameterFreeEventColour_homogeneous
    (arity : ℕ) (c : Label)
    {κ : Type v} [Fintype κ]
    (colour :
      IntrinsicEvent (freeSTree
        (Label := Label) (arity := arity)) → κ) :
    ∃ W : ShapeMap
      (freeSTree (Label := Label) (arity := arity)),
      ∀ F G : ShapeMap
        (freeSTree (Label := Label) (arity := arity)),
        colour (W.mapEvent
          (F.mapEvent (canonicalEmptyEvent (arity := arity) c))) =
        colour (W.mapEvent
          (G.mapEvent (canonicalEmptyEvent (arity := arity) c))) := by
  let χ : Node Label arity → κ :=
    fun a => colour (emptyEventAtNode arity a c)
  obtain ⟨W, hW⟩ :=
    freeHistoryRootColour_homogeneous
      (Label := Label) arity χ
  refine ⟨W, ?_⟩
  intro F G
  simpa only [canonicalEmptyEvent_eq_emptyEventAtNode,
    map_emptyEventAtNode] using hW F G

end StructuralRamsey.Girth
