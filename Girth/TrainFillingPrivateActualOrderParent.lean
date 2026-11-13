import Girth.TrainFillingPrivateCanonicalCutBridge
import Girth.TrainFillingPrivateSelectedOldRange

set_option Elab.async false

/-!
# The actual selected OrderStage parents of the canonical filled train

The lower cutoff-two input is RR_h, hence a true OrderStage with
allCutGirth, not a bare ForestTailStage. Fix its ACTUAL selected
designated copies b of the entire contracted M.

For every selected b the vertex map into N is literally its selected
relational embedding. The old-edge map into N's full A-support is
the one constructed from the SAME b in the previous stage bridge.
The old-image equality needed for the canonical inherited-cut
identification is now a theorem, not a caller hypothesis.

A final arrow still needs the canonical template placement equality,
the selected partite embedding and the original T inside each
choice component. The checked OrderStage filling input separately
supplies the required full system-girth bound at every old cut.
No output girth is assumed here and no edges are removed from N[X].
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Exact original selected parent index of the genuine shorter
OrderStage. It is not a quotient by selected vertex carrier. -/
abbrev ActualOrderParent
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
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed) :=
  {b : DesignatedCopy M D S.system family // b ∈ S.selected}

/-- The genuine selected vertex embedding, with precisely the
selected old parent as its index. -/
noncomputable def actualOrderParentVertex [Nontrivial X]
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
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed) :
    ActualOrderParent U A M T hm hSupport hLinear D
      family allowed S → Vertex U ↪ S.Vertex :=
  fun i => i.1.embedding.toFunctionEmbedding

/-- The entire actual old physical edge map of each selected
OrderStage parent, constructed from that same selected embedding. -/
noncomputable def actualOrderParentOldEdge [Nontrivial X]
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
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    ActualOrderParent U A M T hm hSupport hLinear D
      family allowed S → (C × P) ↪ H.OldEdge :=
  fun i =>
    actualSelectedFilledOldEdgeEmbedding U A M T hm hSupport hLinear
      D family allowed S.toForestTailStage i.1 H hOld

/-- Selected old edge ranges coincide with the complete A-support
carriers contained in the corresponding selected old parent.
This proves exactly the source identity needed by inheritedCutData,
with NO old-range assumption on the actual OrderStage. -/
theorem actualOrderParentOldEdge_range_eq_contained [Nontrivial X]
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
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    ∀ i : ActualOrderParent U A M T hm hSupport hLinear
        D family allowed S,
      Set.range (actualOrderParentOldEdge U A M T hm hSupport
        hLinear D family allowed S H hOld i) =
      {f : H.OldEdge | f.1 ⊆
        Set.range (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i)} := by
  intro i
  change
    Set.range (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S.toForestTailStage
      i.1 H hOld) =
    {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding}
  exact actualSelectedFilledOldEdgeEmbedding_range_eq_contained
    U A M T hm hSupport hLinear D family allowed
      S.toForestTailStage i.1 H hOld

/-- Faithfulness at every actual old train cut for all selected
OrderStage parents. Neither beta_i nor the quotient-wagon reflection
is supplied by the caller. -/
theorem actualOrderParentOldEdge_faithful [Nontrivial X]
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
    (i : ActualOrderParent U A M T hm hSupport hLinear
      D family allowed S)
    (ν : Fin (t.length + 1)) (e f : C × P) :
    (contractedChoiceTrain U T hm).rel ν e f ↔
      (actualSelectedFilledOldTrain U A M T hm hSupport
        hLinear D family allowed S.toForestTailStage H hOld).rel ν
        (actualOrderParentOldEdge U A M T hm hSupport
          hLinear D family allowed S H hOld i e)
        (actualOrderParentOldEdge U A M T hm hSupport
          hLinear D family allowed S H hOld i f) := by
  exact actualSelectedFilledOldTrain_faithful U A M T hm
    hSupport hLinear D family allowed S.toForestTailStage
      i.1 i.2 H hOld ν e f

end StructuralRamsey.Girth.IndexedPrivateChoice
