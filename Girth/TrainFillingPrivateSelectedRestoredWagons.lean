import Girth.TrainFillingPrivateSelectedStageFilling

set_option Elab.async false

/-!
# Actual restored proper wagons of the selected cutoff-two copy

The source-to-actual-N[X] bridge now supplies:
* one old physical edge injection beta from a genuine selected M-copy;
* exact complete old edge carriers;
* faithful train relations at every cut in the actual old train.

The checked TrainFillingIndexedActualRestoredParents reconstruction
therefore builds the genuine proper-wagon injection on the restored
filled train, with no separately invented quotient map.

This deliberately excludes the universal top: it is one shared wagon
for all choice components. The nonempty local-template edge type is
still a genuine application obligation (fulfilled by covered X).
No global parentwise realized designated-copy family is claimed yet.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Construct the selected filled proper-wagon injection at one
non-universal restored cut from the actual selected M-copy.
The original train faithfulness is derived, not a caller premise. -/
noncomputable def actualSelectedRestoredWagonEmbedding [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length) :
    ProperWagon (Q := Quotient (T.wagonSetoid ν)) U ↪
      Quotient
        (((H.toTrainFilling).inheritedTrain
          (actualSelectedFilledOldTrain U A M T hm hSupport hLinear
            D family allowed S H hOld)).wagonSetoid ν.succ) :=
  selectedIndexedRestoredWagonEmbedding U H hTemplate T hm
    (actualSelectedFilledOldTrain U A M T hm hSupport hLinear
      D family allowed S H hOld)
    (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b H hOld)
    ν hProper hLocal
    (actualSelectedFilledOldTrain_faithful U A M T hm
      hSupport hLinear D family allowed S b hb H hOld ν)

/-- The actual selected restored proper-wagon injection commutes
literally with the physical filled-edge parents. No extra
parent-commutation hypothesis is postulated. -/
theorem actualSelectedRestoredWagonEmbedding_parent [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (e : Edge U) :
    actualSelectedRestoredWagonEmbedding U A M T hm
      hSupport hLinear D family allowed S b hb H
        hOld hTemplate hLocal ν hProper
      (properParentOf U
        (fun p => Quotient.mk (T.wagonSetoid ν) p) e) =
      Quotient.mk
        (((H.toTrainFilling).inheritedTrain
          (actualSelectedFilledOldTrain U A M T hm
            hSupport hLinear D family allowed S H hOld)).wagonSetoid ν.succ)
        (selectedIndexedFilledEdgeEmbedding U H hTemplate
          (actualSelectedFilledOldEdgeEmbedding U A M T hm
            hSupport hLinear D family allowed S b H hOld) e) := by
  exact selectedIndexedRestoredWagonEmbedding_parent U H hTemplate
    T hm (actualSelectedFilledOldTrain U A M T hm
      hSupport hLinear D family allowed S H hOld)
    (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b H hOld)
    ν hProper hLocal
    (actualSelectedFilledOldTrain_faithful U A M T hm
      hSupport hLinear D family allowed S b hb H hOld ν) e

end StructuralRamsey.Girth.IndexedPrivateChoice
