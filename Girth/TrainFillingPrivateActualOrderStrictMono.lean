import Girth.TrainFillingIndexedMonotoneCarrierBridge
import Girth.TrainFillingPrivateActualOrderRealization

set_option Elab.async false

/-!
# Selected full-wagon carriers force all filled-edge carriers

In the actual direct cutoff-two construction, the source uses all X
coordinates in each contracted first wagon. The selected shorter
M-copy b maps that COMPLETE carrier onto a genuine N-edge.

When the source placements, b, and the canonical N[X] placements are
strictly increasing in their common (predicate-block) global orders,
finite order-embedding uniqueness gives the pointwise coordinates.
It follows that EVERY physical filled G0 edge, not only selected W*
edges, has precisely its required vertex image. The final parentwise
realization can therefore use the weaker carrier-only interface.

This file removes the unnecessary hypothesis hPlace/hEdgeCarrier
from the actual OrderStage application, replacing it by genuine,
separately auditable monotonicity properties of the selected embeddings.

This is candidate Lean source. The OrderStage output does NOT itself
assert these global monotonicities: the ordered relational
presentation and canonical placement must supply them. No output
girth or selected Ramsey arrow is assumed here.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- At every selected old parent, the actual old-edge carrier equation
provides the whole-carrier hypothesis of the already checked finite
ordered-placement uniqueness theorem. -/
theorem actualOrderParent_filledEdgeCarrier_of_strictMono
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
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hSelectedMono : ∀ i : ActualOrderParent U A M T hm
        hSupport hLinear D family allowed S,
      StrictMono (fun z : Vertex U =>
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i) z))
    (hCanonicalMono : ∀ f : H.OldEdge, StrictMono (H.place f))
    (i : ActualOrderParent U A M T hm hSupport hLinear
      D family allowed S)
    (a : Edge U) :
    (selectedIndexedFilledEdgeEmbedding U H hTemplate
      (actualOrderParentOldEdge U A M T hm hSupport hLinear
        D family allowed S H hOld i) a).1 =
      (actualOrderParentVertex U A M T hm hSupport hLinear
        D family allowed S i) '' edgeCarrier U a := by
  let vertex : Vertex U ↪o S.Vertex :=
    OrderEmbedding.ofStrictMono
      (fun z => (actualOrderParentVertex U A M T hm
        hSupport hLinear D family allowed S i) z) (hSelectedMono i)
  let β : (C × P) ↪ H.OldEdge :=
    actualOrderParentOldEdge U A M T hm hSupport hLinear
      D family allowed S H hOld i
  have hRange (cp : C × P) :
      Set.range (fun x : X =>
        vertex (tagVertex U cp.1 ((U cp.1).place cp.2 x))) =
          Set.range (H.place (β cp)) := by
    calc
      Set.range (fun x : X =>
        vertex (tagVertex U cp.1 ((U cp.1).place cp.2 x))) =
          (fun z : Vertex U => vertex z) '' contractedCarrier U cp := by
            ext y
            constructor
            · rintro ⟨x, rfl⟩
              exact ⟨tagVertex U cp.1 ((U cp.1).place cp.2 x),
                ⟨(U cp.1).place cp.2 x, ⟨x, rfl⟩, rfl⟩, rfl⟩
            · rintro ⟨z, ⟨w, ⟨x, rfl⟩, rfl⟩, rfl⟩
              exact ⟨x, rfl⟩
      _ = (β cp).1 := by
        exact (actualSelectedFilledOldEdgeEmbedding_carrier
          U A M T hm hSupport hLinear D family allowed
            S.toForestTailStage i.1 H hOld cp).symm
      _ = Set.range (H.place (β cp)) := (H.range_place (β cp)).symm
  exact selectedIndexedFilledEdgeEmbedding_carrier_of_strictMono
    U H hTemplate β vertex hSourceMono
    (fun cp => hCanonicalMono (β cp)) hRange a

/-- The complete actual selected OrderStage parentwise realization
is constructed from order compatibility (as in the original paper),
without assuming a pointwise placement equation, an arbitrary physical
carrier map, or any output system-girth bound. -/
noncomputable def actualOrderStageFaithfulParentwise_of_strictMono
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
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length) :
    FaithfulParentwisePhysicalRealization U
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
      (canonicalFilledSelectedData U H
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S)
        (actualOrderParentOldEdge U A M T hm
          hSupport hLinear D family allowed S H hOld)
        (actualSelectedFilledOldTrain U A M T hm
          hSupport hLinear D family allowed S.toForestTailStage
            H hOld) ν) :=
  actualOrderStageFaithfulParentwise_of_carrier
    U A M T hm hSupport hLinear D family allowed S
      H hOld hTemplate hLocal ν hProper
      (actualOrderParent_filledEdgeCarrier_of_strictMono
        U A M T hm hSupport hLinear D family allowed S
          H hOld hTemplate hSourceMono hSelectedMono hCanonicalMono)

end StructuralRamsey.Girth.IndexedPrivateChoice
