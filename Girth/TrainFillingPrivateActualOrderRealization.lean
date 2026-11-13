import Girth.TrainFillingPrivateActualOrderParent
import Girth.TrainFillingPrivateCanonicalCutBridge

set_option Elab.async false

/-!
# Complete faithful parentwise realization from one genuine OrderStage

The old selected-index type, vertex maps, and physical edge maps are
now fixed by the selected copies of the ACTUAL shorter OrderStage.
The exact old-edge range and ALL train-cut reflection follow from
previous proof adapters; they are not independent premises.

The single outstanding pointwise input for this theorem is the
canonical X-coordinate placement compatibility between each
selected original first wagon and the filled target. This follows
from complete ordered-carrier uniqueness after the actual ordered
source/target models have been identified, but is not assumed to
hold for arbitrary nonordered relational embeddings.

For each restored proper cut, this theorem builds the complete
FaithfulParentwisePhysicalRealization record (vertex and edge
injections, exact full carriers/copyEdges and genuine wagon parents).
Different selected old M-copies may overlap; no ambient edge is
removed and no output system-girth is assumed.

The all-cut bound of the OrderStage is applied only after identifying
the checked canonical filling's inheritedCutData with the record here.
This theorem is a candidate pending an exact-head Lean build.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The actual OrderStage supplies all parent maps and range data.
This version requires ONLY exact physical carrier transport,
which the existing ordered-carrier theorem can derive. -/
/-- An actual selected OrderStage constructs every field of the
parentwise realization at one proper restored cut. Neither old-edge
range, selected vertex map, edge map, wagon map, nor cut reflection
is an application premise; all come from the SAME selected stage. -/
noncomputable def actualOrderStageFaithfulParentwise_of_carrier [Nontrivial X]
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
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (hEdgeCarrier : ∀ (i : ActualOrderParent U A M T hm
                     hSupport hLinear D family allowed S)
                   (a : Edge U),
      (selectedIndexedFilledEdgeEmbedding U H hTemplate
        (actualOrderParentOldEdge U A M T hm
          hSupport hLinear D family allowed S H hOld i) a).1 =
      (actualOrderParentVertex U A M T hm
        hSupport hLinear D family allowed S i) '' edgeCarrier U a) :
    FaithfulParentwisePhysicalRealization U
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
      (canonicalFilledSelectedData U H
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S)
        (actualOrderParentOldEdge U A M T hm
          hSupport hLinear D family allowed S H hOld)
        (actualSelectedFilledOldTrain U A M T hm
          hSupport hLinear D family allowed S.toForestTailStage
            H hOld) ν) := by
  let vertex := actualOrderParentVertex U A M T hm
    hSupport hLinear D family allowed S
  let β := actualOrderParentOldEdge U A M T hm
    hSupport hLinear D family allowed S H hOld
  let oldTrain := actualSelectedFilledOldTrain U A M T hm
    hSupport hLinear D family allowed S.toForestTailStage H hOld
  exact canonicalFilledSelectedFaithfulRealization_of_carrier
    U H hTemplate vertex β T hm oldTrain ν hProper hLocal
    (fun i a b => actualOrderParentOldEdge_faithful
      U A M T hm hSupport hLinear D family allowed
        S H hOld i ν a b)
    hEdgeCarrier


/-- An actual selected OrderStage constructs every field of the
parentwise realization at one proper restored cut. Neither old-edge
range, selected vertex map, edge map, wagon map, nor cut reflection
is an application premise; all come from the SAME selected stage. -/
noncomputable def actualOrderStageFaithfulParentwise [Nontrivial X]
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
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (hPlace : ∀ (i : ActualOrderParent U A M T hm
                   hSupport hLinear D family allowed S)
                 (c : C) (p : P) (x : X),
      H.place ((actualOrderParentOldEdge U A M T hm
        hSupport hLinear D family allowed S H hOld i) (c, p)) x =
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i)
          (tagVertex U c ((U c).place p x))) :
    FaithfulParentwisePhysicalRealization U
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
      (canonicalFilledSelectedData U H
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S)
        (actualOrderParentOldEdge U A M T hm
          hSupport hLinear D family allowed S H hOld)
        (actualSelectedFilledOldTrain U A M T hm
          hSupport hLinear D family allowed S.toForestTailStage
            H hOld) ν) := by
  exact actualOrderStageFaithfulParentwise_of_carrier
    U A M T hm hSupport hLinear D family allowed S H hOld
      hTemplate hLocal ν hProper
    (fun i a =>
      selectedIndexedFilledEdgeEmbedding_carrier U H hTemplate
        (actualOrderParentOldEdge U A M T hm
          hSupport hLinear D family allowed S H hOld i)
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i)
        (hPlace i) a)

end StructuralRamsey.Girth.IndexedPrivateChoice
