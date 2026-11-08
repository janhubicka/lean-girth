import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingIndexedEdgeFlatten
import Girth.TrainFillingColourWord

set_option Elab.async false

/-!
# Fixed filling colour words on ACTUAL heterogeneous selected G0 edges

The final cutoff-two Ramsey arrow colours each old N-edge f by the
COMPLETE function e ↦ χ(H.edgeEquiv(f,e)) on all local X-template
edges. The shorter Ramsey witness selects an M-copy on which that
entire function is constant. The first (EHN) Ramsey input selects
one target W* whose actual local template edges have one colour in
that common function.

This module identifies those colour-word coordinates with the
genuine physical selected G0 edges via the already checked
heterogeneous `edgeIndexEquiv` and constructed
`selectedIndexedFilledEdgeEmbedding`. It does not assume an
independently supplied output edge map or require selected template
edge sets to be identical for different choices or old wagons.

The theorem is a conditional exact colour-transport identity:
constructing the selected M-copy, choosing the EHN W* by the
appropriate finite Ramsey arrow and proving its faithful target
realisation are separate parts of the final proof.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v w
variable {C V P X Y : Type v} {κ : Type w}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)

/-- For one chosen W* component c, a constant COMPLETE colour word
on every selected first-wagon old edge and a monochromatic selected
local template edge family force monochromaticity on EVERY actual
physical G0 target edge over that component.

The source output is a physical edge in H's complete filled family;
it is neither an abstract pair of labels nor a new assumed edge map. -/
theorem selectedIndexedTargetEdges_colourWord_constant
    (β : (C × P) ↪ H.OldEdge)
    (χ : H.toTrainFilling.NewEdge → κ)
    (ρ : H.TemplateEdge → κ)
    (c : C) (colour : κ)
    (hWords : ∀ p : P, H.colourWord χ (β (c, p)) = ρ)
    (hLocal : ∀ p : P, ∀ e : H.TemplateEdge,
      e ∈ selectedCommonEdges U H.templateEdges hTemplate c p →
      ρ e = colour) :
    ∀ a : Edge U, a ∈ targetEdges U c →
      χ (selectedIndexedFilledEdgeEmbedding U H hTemplate β a) =
        colour := by
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  let t : H.TemplateEdge :=
    (edgeIndexEquiv U H.templateEdges hTemplate (tagEdge U c a₀)).2
  have ht : t ∈ selectedCommonEdges U H.templateEdges hTemplate
      c a₀.1 := by
    exact (selectedCommonEdges_iff U H.templateEdges hTemplate
      (tagEdge U c a₀)).mp ha₀
  change χ (H.edgeEquiv (β (c, a₀.1), t)) = colour
  calc
    χ (H.edgeEquiv (β (c, a₀.1), t)) =
        H.colourWord χ (β (c, a₀.1)) t := rfl
    _ = ρ t := congrFun (hWords a₀.1) t
    _ = colour := hLocal a₀.1 t ht


/-- The literal TWO-ARROW composition for the complete physical
heterogeneous G0 target.

The shorter ordered Ramsey witness chooses an embedding of ALL
contracted first wagons with the SAME complete X-template colour word.
The first EHN Ramsey witness then chooses one W* component whose
selected local template edges are monochromatic in that word.

Under exactly these two arrow interfaces, the entire genuinely
selected physical G0 target edge set is monochromatic in H. No
separate output physical edge map or pointwise carrier equation is
assumed. This is the final colour calculation; existence of the
older edge-arrow and EHN-arrow inputs is checked in their own modules,
while their simultaneous prescribed-target strongness and wagon
geometry are part of the remaining end-to-end application. -/
theorem selectedIndexedTargetEdges_ramsey_of_two_arrows
    (hOldArrow :
      ∀ word : H.OldEdge → H.TemplateEdge → κ,
        ∃ (β : (C × P) ↪ H.OldEdge)
          (ρ : H.TemplateEdge → κ),
          ∀ cp : C × P, word (β cp) = ρ)
    (hLocalArrow :
      ∀ ρ : H.TemplateEdge → κ,
        ∃ (c : C) (colour : κ),
          ∀ p : P, ∀ e : H.TemplateEdge,
            e ∈ selectedCommonEdges U H.templateEdges hTemplate c p →
              ρ e = colour)
    (χ : H.toTrainFilling.NewEdge → κ) :
    ∃ (β : (C × P) ↪ H.OldEdge) (c : C) (colour : κ),
      ∀ a : Edge U, a ∈ targetEdges U c →
        χ (selectedIndexedFilledEdgeEmbedding U H hTemplate β a) =
          colour := by
  obtain ⟨β, ρ, hWords⟩ := hOldArrow (H.colourWord χ)
  obtain ⟨c, colour, hLocal⟩ := hLocalArrow ρ
  refine ⟨β, c, colour, ?_⟩
  exact selectedIndexedTargetEdges_colourWord_constant
    U H hTemplate β χ ρ c colour
    (fun p => hWords (c, p)) hLocal


end StructuralRamsey.Girth.IndexedPrivateChoice
