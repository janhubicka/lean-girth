import Girth.ForestRootColourCanon
import Girth.ForestParameterFreeOrbit
import Mathlib.Tactic

/-!
# No one free shape map homogenises all finite widths simultaneously

For every fixed k, finite-dimensional successor-tree Ramsey homogenises
the Boolean colour recording whether the image of the root has level k.
However, no ONE free shape map homogenises this family for ALL k≥1.
Given W, set k to the level of W of a one-step source child. Then
the identity and the one-step root-moving map have opposite colours.

This refutes a naive attempt to replace bounded presentations of all
marked B-history types by unrestricted countable fusion of separately
homogeneous finite widths. It leaves open special fusion for geometric
profile colourings with additional coherence hypotheses.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u
variable {Label : Type u} [Fintype Label] [Nonempty Label]

/-- Each fixed root-level Boolean colouring admits a homogeneous
free shape reduction. -/
theorem fixedRootLevelColour_homogeneous
    (arity k : ℕ) :
    ∃ W : ShapeMap
      (freeSTree (Label := Label) (arity := arity)),
      ∀ F G : ShapeMap
        (freeSTree (Label := Label) (arity := arity)),
        decide ((W (F (rootNode (Label := Label)
          (arity := arity)))).level = k) =
        decide ((W (G (rootNode (Label := Label)
          (arity := arity)))).level = k) := by
  exact freeHistoryRootColour_homogeneous
    (Label := Label) arity
    (χ := fun a : Node Label arity => decide (a.level = k))

/-- Even though each width is individually Ramsey, there is no
uniform free shape reduction making every root-level-width
colouring homogeneous simultaneously. -/
theorem noUniformAllWidthRootHomogeneity
    (arity : ℕ) :
    ¬ ∃ W : ShapeMap
      (freeSTree (Label := Label) (arity := arity)),
      ∀ k : ℕ, 0 < k →
        ∀ F G : ShapeMap
          (freeSTree (Label := Label) (arity := arity)),
        decide ((W (F (rootNode (Label := Label)
          (arity := arity)))).level = k) =
        decide ((W (G (rootNode (Label := Label)
          (arity := arity)))).level = k) := by
  rintro ⟨W, hW⟩
  let c : Label := Classical.choice
    (inferInstance : Nonempty Label)
  let h : History Label arity 1 :=
    History.step History.root
      ⟨c, emptyParamTuple arity 0⟩
  obtain ⟨D, hD⟩ :=
    exists_free_shape_from_root (Label := Label)
      (arity := arity) 1 h
  let root : Node Label arity := rootNode
  let b : Node Label arity := ⟨1, h⟩
  have hRootLt : root.level < b.level := by
    change 0 < 1
    omega
  have hImageLt :
      (W root).level < (W b).level :=
    W.level_lt_of_level_lt hRootLt
  let k : ℕ := (W b).level
  have hk : 0 < k := Nat.zero_lt_of_lt hImageLt
  have hDroot : D root = b := hD
  have hColour := hW k hk
    (ShapeMap.id (freeSTree (Label := Label) (arity := arity))) D
  change decide ((W root).level = k) =
    decide ((W (D root)).level = k) at hColour
  rw [hDroot] at hColour
  have hNot : (W root).level ≠ k := ne_of_lt hImageLt
  simp [k, hNot] at hColour

end StructuralRamsey.Girth
