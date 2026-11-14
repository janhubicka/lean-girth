import Girth.TrainFillingIndexedParentwiseRealization

set_option Elab.async false

/-!
# Monochromaticity of the actual labelled scattered target

The indexed two-arrow calculation produces one selected old parent i
and one local EHN choice c. It proves the colour of each genuinely
selected local physical G0 edge after the parent's edge embedding.

Global scattering preserves the pair (i,c) as a designated LABEL.
Its designated family's physical copyEdges field is the exact
image of the selected local edge family under that same embedding.

This elementary theorem transports the colour statement to the
actual (i,c)-labelled target in the unchanged global ambient system.
It does not assert existence of the parentwise realization, which
the adjacent Track 5 canonical and actual OrderStage modules
construct under their precise geometric premises.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice.ParentwiseRealization

universe v w

variable {C V P X Q GV GE I GQ : Type v} {κ : Type w}
variable {U : C → PrivateWagonInput V P X}
variable {parent : P → Q}
variable {D : OrderOneData GV GE I GQ}

/-- Every actual designated edge of label (old parent, local choice)
is the image of an actual selected local edge, so the colour is
constant on the complete labelled target, not just on a phantom
set of template pairs. -/
theorem designatedTarget_monochromatic
    (R : ParentwiseRealization U parent D)
    (χ : GE → κ) (i : I) (c : C) (colour : κ)
    (hMono : ∀ a : Edge U, a ∈ targetEdges U c →
      χ (R.edge i a) = colour) :
    ∀ e : GE, e ∈ R.designatedFamily.target.copyEdges (i, c) →
      χ e = colour := by
  intro e he
  change e ∈ R.targetEdges (i, c) at he
  obtain ⟨a, ha, rfl⟩ := he
  exact hMono a ha

end StructuralRamsey.Girth.IndexedPrivateChoice.ParentwiseRealization
