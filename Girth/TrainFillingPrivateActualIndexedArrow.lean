import Girth.TrainFillingPrivateActualWordArrow
import Girth.TrainFillingPrivateSelectedIndexedArrow

set_option Elab.async false

/-!
# Exact indexed two-arrow colouring from a genuine shorter OrderStage

The first (EHN) Ramsey arrow supplies a selected copy of the
DISJOINT UNION W inside X. Its selected local template edges
are monochromatic under one complete word rho.

The second (shorter OrderStage) arrow on words yields a GENUINE
selected parent b : M -> N and equality of the complete X-edge
colour word on EVERY contracted first-wagon edge in b(M).

This theorem composes the two arrows with the checked literal
physical edge-colour transfer, retaining:
  * the same selected parent b in N;
  * the same selected local choice c (one copy of W) in X;
  * the actual physical G0 target edge set of component c;
  * no deletion of other ambient N[X] edges.

Thus the output is indexed by (b,c), not just an unlabelled
monochromatic subset. The construction of its vertex embedding
and proof of all original train/partite relations belong to the
faithful parentwise realization, not to this colour calculation.

Candidate source; a local Lean build and axiom audit are required.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The final physical colour calculation with a GENUINE selected
OrderStage parent and a common EHN choice. This does not assume
a preselected injection beta into N's old physical edges. -/
theorem actualOrderStage_indexedFilledColourArrow
    [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (κ : Type w)
    (hSourceA : Nonempty (Embedding A M))
    (hLowerArrow : TrainRecursiveWitness.DesignatedArrow
      S.toForestTailStage (H.TemplateEdge → κ))
    (hLocalArrow : ∀ ρ : H.TemplateEdge → κ,
      ∃ (c : C) (colour : κ),
        ∀ p : P, ∀ e : H.TemplateEdge,
          e ∈ selectedCommonEdges U H.templateEdges
            hTemplate c p → ρ e = colour)
    (χ : H.toTrainFilling.NewEdge → κ) :
    ∃ (b : DesignatedCopy M D S.system family),
      b ∈ S.selected ∧
        ∃ (c : C) (colour : κ),
          ∀ a : Edge U, a ∈ targetEdges U c →
            χ (selectedIndexedFilledEdgeEmbedding U H hTemplate
              (actualSelectedFilledOldEdgeEmbedding U A M T hm
                hSupport hLinear D family allowed
                S.toForestTailStage b H hOld) a) = colour := by
  obtain ⟨b, hb, ρ, hWords⟩ :=
    actualOrderStage_oldColourWordArrow_indexed U A M T hm
      hSupport hLinear D family allowed S H hOld κ
      hSourceA hLowerArrow (H.colourWord χ)
  obtain ⟨c, colour, hMono⟩ := hLocalArrow ρ
  refine ⟨b, hb, c, colour, ?_⟩
  exact selectedIndexedTargetEdges_colourWord_constant
    U H hTemplate
    (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S.toForestTailStage b H hOld)
    χ ρ c colour (fun p => hWords (c, p)) hMono

end StructuralRamsey.Girth.IndexedPrivateChoice
