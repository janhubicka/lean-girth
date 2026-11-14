import Girth.TrainFillingPrivateActualOrderStrictMono
import Girth.TrainFillingPrivateActualIndexedArrow
import Girth.TrainFillingPrivateParentwiseColour

set_option Elab.async false

/-!
# The actual (selected old parent, EHN choice) labelled Ramsey arrow

The lower shorter OrderStage supplies a genuine selected M-copy b,
on which ALL old N edges have the same complete X-template colour
word. The EHN local arrow chooses ONE W-embedding c in X on which
all original first-wagon selected local edges have one colour.

The exact old first-wagon carriers and the order compatibility of
the genuine selected b determine the full G0-to-H filled vertex
and physical edge maps. The global parentwise constructor then
realizes every target with its ACTUAL label (b,c), retaining all
ambient H edges and all proper-wagon quotient names.

We prove monochromaticity directly for the labelled designated
target family constructed by that parentwise realization, not
merely for an auxiliary set of template-edge pairs. The same
selected parent b and choice c occur in the two-arrow conclusion
and the final designated target label.

What remains at the application is to construct the actual ordered
colour-block M (with its exact A-support and correct train
parameters), supply the genuine lower RR_h OrderStage and EHN
Ramsey inputs, and identify the selected target T and all cut
bounds with the actual paper statement. This source is not
kernel checked until local Lean compilation.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The TWO actual Ramsey selections yield a monochromatic copy
in the COMPLETE labelled parentwise designated family:
an existing lower parent and one existing EHN choice, not
an invented pair or a separately selected set of physical edges.

The selected vertex and carrier maps are derived from the source
and target global orders, so no actual H-edge map or copy-edge
range is an independent application premise. -/
theorem actualOrderStage_labelledTargetColourArrow
    [Nontrivial X] [Finite X] [LinearOrder X] [LinearOrder (Vertex U)]
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
    [PartialOrder S.Vertex]
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hSelectedMono : ∀ i : ActualOrderParent U A M T hm
        hSupport hLinear D family allowed S,
      StrictMono (fun z : Vertex U =>
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i) z))
    (hCanonicalMono : ∀ f : H.OldEdge, StrictMono (H.place f))
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (κ : Type w)
    (hCP : Nonempty (C × P))
    (hLowerArrow : TrainRecursiveWitness.DesignatedArrow
      S.toForestTailStage (H.TemplateEdge → κ))
    (hLocalArrow : ∀ ρ : H.TemplateEdge → κ,
      ∃ (c : C) (colour : κ),
        ∀ p : P, ∀ e : H.TemplateEdge,
          e ∈ selectedCommonEdges U H.templateEdges
            hTemplate c p → ρ e = colour) :
    let Real := actualOrderStageFaithfulParentwise_of_strictMono
      U A M T hm hSupport hLinear D family allowed S
        H hOld hTemplate hLocal hSourceMono hSelectedMono
          hCanonicalMono ν hProper
    ∀ χ : H.toTrainFilling.NewEdge → κ,
      ∃ (i : ActualOrderParent U A M T hm
           hSupport hLinear D family allowed S)
        (c : C) (colour : κ),
        ∀ e : H.toTrainFilling.NewEdge,
          e ∈ Real.toParentwiseRealization.designatedFamily.target.copyEdges (i,c) →
            χ e = colour := by
  let Real := actualOrderStageFaithfulParentwise_of_strictMono
    U A M T hm hSupport hLinear D family allowed S
      H hOld hTemplate hLocal hSourceMono hSelectedMono
        hCanonicalMono ν hProper
  intro χ
  obtain ⟨b, hb, c, colour, hMono⟩ :=
    actualOrderStage_indexedFilledColourArrow
      U A M T hm hSupport hLinear D family allowed S
        H hOld hTemplate κ hCP hLowerArrow hLocalArrow χ
  let i : ActualOrderParent U A M T hm
      hSupport hLinear D family allowed S := ⟨b, hb⟩
  refine ⟨i, c, colour, ?_⟩
  apply Real.toParentwiseRealization.designatedTarget_monochromatic
    χ i c colour
  intro a ha
  change χ (selectedIndexedFilledEdgeEmbedding U H hTemplate
    (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S.toForestTailStage
      b H hOld) a) = colour
  exact hMono a ha

end StructuralRamsey.Girth.IndexedPrivateChoice
