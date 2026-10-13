import Girth.TrainInteriorParentQuotientBridge
import Girth.TrainActualTopParentQuotientBridge

/-!
# Interior parent bridges in the actual active relational attachment

Discharge physical shared-edge equality and pointwise coverage using the
existing actual A-support attachment theorems. The only new witness
premise is the exact order-one bound at the parent cut. The universal top
continues to use activeAttached_topParent_twoSourceBridge without it.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- Actual active-attachment interior bridge, not an abstract carrier model. -/
theorem activeAttached_interiorParent_twoSourceBridge
    {m : ℕ}
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding
      (B.toRelStructure.induce (activeCarrier A B α)) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B.toRelStructure) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hRel : ∀ (κ : Fin (m + 1)) (i : I)
      (s t : SharedOldACarrierEdge A B.toRelStructure (activeCarrier A B α)),
      oldTrain.rel κ
        (sharedOldACarrierInclusion A B.toRelStructure (activeCarrier A B α) s)
        (sharedOldACarrierInclusion A B.toRelStructure (activeCarrier A B α) t) ↔
      coreTrain.rel κ
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i s)
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i t))
    (allowed : Set (RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I)))
    (hOrderOne : (sharedWitnessOrderOneData coreTrain ν
      (sharedOldACarrierCoreEmbedding A B.toRelStructure
        (activeCarrier A B α) D f)
      (attachedCoreAEdgeCarrier A B.toRelStructure
        (activeCarrier A B α) D f)).Bound) :
    ParentCoreTwoSourceBridge
      (fun i => oldTrain.wagonClassCarrier
        (attachedOldAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f i) μ)
      (oldTrain.wagonParent μ ν hμν)
      (coreTrain.wagonClassCarrier
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f) μ)
      (coreTrain.wagonParent μ ν hμν)
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel oldTrain μ
          (fun _ : I => sharedOldACarrierInclusion
            A B.toRelStructure (activeCarrier A B α)))
        (oldSharedWagonLabel coreTrain μ
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D f))))
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel oldTrain ν
          (fun _ : I => sharedOldACarrierInclusion
            A B.toRelStructure (activeCarrier A B α)))
        (oldSharedWagonLabel coreTrain ν
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D f))))
      (copyCarrier (RelStructure.Attachment.coreEmbedding
        B.toRelStructure (activeCarrier A B α) D f))
      allowed := by
  apply interiorParent_twoSourceBridge_of_orderOne
    oldTrain coreTrain μ ν hμν
    (fun _ : I => sharedOldACarrierInclusion
      A B.toRelStructure (activeCarrier A B α))
    (sharedOldACarrierCoreEmbedding A B.toRelStructure
      (activeCarrier A B α) D f)
    hRel
    (attachedOldAEdgeCarrier A B.toRelStructure (activeCarrier A B α) D f)
    (attachedCoreAEdgeCarrier A B.toRelStructure (activeCarrier A B α) D f)
    (by
      intro i s
      exact attachedSharedAEdgeCarrier_eq A B.toRelStructure
        (activeCarrier A B α) D f i s)
    (copyCarrier (RelStructure.Attachment.coreEmbedding
      B.toRelStructure (activeCarrier A B α) D f))
    allowed
    (by
      intro i e z hzCore hzOld
      exact activeAttached_sharedOldAEdge_at_coreVertex
        A B α D f i e z hzCore hzOld)
    hOrderOne

end StructuralRamsey.Girth
