import Girth.TrainActualParameterPremises
import Girth.TrainActualActiveSharedEdge
import Girth.TrainSharedSupportInteriorCompatibility

/-!
# Actual generated parameters from intrinsic inductive data

This composes the existing generated-train parameter theorem with the
intrinsic-to-attached premise bridges.  The assumptions now concern the
old picture and the core witness on their original vertex sets, with one
common sequence of allowed parts.  An actual projected A-copy supplies the
nonempty shared support.  Train compatibility is required only at interior
cuts; equality at the bottom and the universal top supply the endpoints.

The remaining core order-one bounds are genuine inductive hypotheses,
required only at interior cuts.  There is no extra top cycle coordinate,
no pruning of the physical A-support edge family, and no claim here that
the core witness or its system-girth bounds have been constructed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- The actual active attachment preserves all adjacent allowed-part
parameters from intrinsic old/core bounds, interior train compatibility,
and intrinsic core order-one bounds.  All extrinsic carrier premises,
nonempty shared-support premises, and endpoint compatibility premises of
the existing generated-train theorem are proved internally. -/
theorem activeAttached_actualASupport_allAdjacentParameters_of_intrinsic
    {m : ℕ}
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A B α)
    (D : StructuralRamsey.Partite.System L P Core)
    (f : I → StructuralRamsey.Partite.Embedding
      (B.induce (activeCarrier A B α)) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B.toRelStructure) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D.toRelStructure) m)
    (allowedParts : Fin (m + 1) → Set P)
    (hOld : oldTrain.AdjacentParameters
      (fun e : OldACarrierEdge A B.toRelStructure => e.1)
      (fun ν => {x | B.part x ∈ allowedParts ν}))
    (hCore : coreTrain.AdjacentParameters
      (fun e : OldACarrierEdge A D.toRelStructure => e.1)
      (fun ν => {x | D.part x ∈ allowedParts ν}))
    (hInterior : ∀ κ : Fin (m + 1), 0 < κ.val → κ.val < m →
      ∀ (i : I)
        (s t : SharedOldACarrierEdge A B.toRelStructure
          (activeCarrier A B α)),
        oldTrain.rel κ
          (sharedOldACarrierInclusion A B.toRelStructure
            (activeCarrier A B α) s)
          (sharedOldACarrierInclusion A B.toRelStructure
            (activeCarrier A B α) t) ↔
        coreTrain.rel κ
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D.toRelStructure
            (fun i => (f i).toEmbedding) i s)
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D.toRelStructure
            (fun i => (f i).toEmbedding) i t))
    (hOrderOne : ∀ ν : Fin (m + 1), 0 < ν.val → ν.val < m →
      (sharedWitnessOrderOneData coreTrain ν
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D.toRelStructure
          (fun i => (f i).toEmbedding))
        (fun e : OldACarrierEdge A D.toRelStructure => e.1)).Bound) :
    (generatedActualASupportTrain A hA B.toRelStructure
      (activeCarrier A B α) D.toRelStructure
      (fun i => (f i).toEmbedding) oldTrain coreTrain
      (activeCarrier_all_standard_copies_meet_core A B α active I)).AdjacentParameters
        (fun e : ActualAttachedAEdge A B.toRelStructure
          (activeCarrier A B α) D.toRelStructure
          (fun i => (f i).toEmbedding) => e.1)
        (fun ν => {x |
          (StructuralRamsey.Partite.Attachment.attach
            B (activeCarrier A B α) D f).part x ∈ allowedParts ν}) := by
  have hRel : ∀ κ : Fin (m + 1), ∀ (i : I)
      (s t : SharedOldACarrierEdge A B.toRelStructure
        (activeCarrier A B α)),
      oldTrain.rel κ
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) s)
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) t) ↔
      coreTrain.rel κ
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D.toRelStructure
          (fun i => (f i).toEmbedding) i s)
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D.toRelStructure
          (fun i => (f i).toEmbedding) i t) := by
    apply sharedSupportTrainRel_of_interior oldTrain coreTrain
      (sharedOldACarrierInclusion A B.toRelStructure (activeCarrier A B α))
      (sharedOldACarrierCoreEmbedding A B.toRelStructure
        (activeCarrier A B α) D.toRelStructure (fun i => (f i).toEmbedding))
    intro κ hZero hTop i s t
    exact hInterior κ (by omega) (by omega) i s t
  exact activeAttached_actualASupport_allAdjacentParameters_of_orderOne
    A hA B α D.toRelStructure (fun i => (f i).toEmbedding)
    oldTrain coreTrain
    (activeCarrier_all_standard_copies_meet_core A B α active I)
    hRel
    (fun ν => {x |
      (StructuralRamsey.Partite.Attachment.attach
        B (activeCarrier A B α) D f).part x ∈ allowedParts ν})
    (fun i => attachedOldAEdgeCarrier_adjacentParameters_of_intrinsic
      A B (activeCarrier A B α) D f oldTrain allowedParts hOld i)
    (attachedCoreAEdgeCarrier_adjacentParameters_of_intrinsic
      A B (activeCarrier A B α) D f coreTrain allowedParts hCore)
    (fun ν hPos hLt => attachedSharedWitnessOrderOne_bound_of_intrinsic
      A B.toRelStructure (activeCarrier A B α) D.toRelStructure
      (fun i => (f i).toEmbedding) coreTrain ν (hOrderOne ν hPos hLt))

end StructuralRamsey.Girth
