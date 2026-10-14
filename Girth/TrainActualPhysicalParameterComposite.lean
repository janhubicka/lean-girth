import Girth.TrainPhysicalParameterBridgeComposite
import Girth.TrainActualWagonCarrierGeometry
import Girth.TrainActualInteriorParentQuotientBridge

/-!
# Physical generated train parameter in the actual active A-support attachment

Eliminate the abstract carrier-owner and shared-edge bridge premises
of the physical composition theorem using the actual relational free
attachment geometry. The one remaining local witness hypothesis is
the exact order-one bound at the chosen parent cut. The old/core sibling
parameters, reflection, and the two physical carrier agreement
identities remain explicit.

This proves a bound for the presented physical A-support wagon classes.
Transport to the actual attached A-carrier hypergraph is a separate
representation step. It does not prove full A1--A3 system girth.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- For a genuine active partite attachment, the order-one witness
bound suffices for the sibling parameter at the physical pushout cut.
All source carrier geometry is discharged internally. -/
theorem activeAttached_physicalGenerated_parentBound_of_orderOne
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
    (hShared : ∀ i : I,
      Nonempty (SharedOldACarrierEdge A B.toRelStructure
        (activeCarrier A B α)))
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      oldTrain.rel κ
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) s)
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) t) ↔
      coreTrain.rel κ
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i s)
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i t))
    (physicalEdges :
      ActualAPicturePushoutEdge A B.toRelStructure
        (activeCarrier A B α) D I →
      Set (RelStructure.Attachment.Vertex
        (activeCarrier A B α) (W := Core) (I := I)))
    (hCorePhysical : ∀ b,
      physicalEdges
        (physicalCoreEdge
          (sharedOldACarrierInclusion A B.toRelStructure
            (activeCarrier A B α)) I b) =
        attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f b)
    (hStdPhysical : ∀ i a,
      physicalEdges
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B.toRelStructure
            (activeCarrier A B α))
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D f) i a) =
        attachedOldAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f i a)
    (allowed : Set (RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I)))
    (hOld : ∀ i : I,
      TrainParentIntersectionBound
        (oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B.toRelStructure
            (activeCarrier A B α) D f i) μ)
        (oldTrain.wagonParent μ ν hμν) allowed)
    (hCore : TrainParentIntersectionBound
      (coreTrain.wagonClassCarrier
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f) μ)
      (coreTrain.wagonParent μ ν hμν) allowed)
    (hOrderOne :
      (sharedWitnessOrderOneData coreTrain ν
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f)).Bound) :
    TrainParentIntersectionBound
      ((physicalPictureGeneratedTrain oldTrain coreTrain
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α))
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        hShared).wagonClassCarrier physicalEdges μ)
      ((physicalPictureGeneratedTrain oldTrain coreTrain
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α))
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        hShared).wagonParent μ ν hμν) allowed := by
  let S := activeCarrier A B α
  let oldCarrier := attachedOldAEdgeCarrier A B.toRelStructure S D f
  let coreCarrier := attachedCoreAEdgeCarrier A B.toRelStructure S D f
  let coreVertices := copyCarrier
    (RelStructure.Attachment.coreEmbedding B.toRelStructure S D f)
  apply physicalGenerated_parentIntersectionBound_of_orderOne
    oldTrain coreTrain μ ν hμν
    (sharedOldACarrierInclusion A B.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A B.toRelStructure S D f)
    hShared hRel
    oldCarrier coreCarrier physicalEdges
    hCorePhysical hStdPhysical coreVertices allowed
    hOld hCore
  · intro c
    exact attachedCoreAWagon_carrier_subset_core
      A B.toRelStructure S D f coreTrain μ c
  · intro i j a b x hx hi hj
    exact attachedOldAWagon_offCore_index_unique
      A B.toRelStructure S D f oldTrain μ
      i j a b x hx hi hj
  · intro i s
    exact attachedSharedAEdgeCarrier_eq
      A B.toRelStructure S D f i s
  · intro i e x hxCore hxOld
    exact activeAttached_sharedOldAEdge_at_coreVertex
      A B α D f i e x hxCore hxOld
  · exact hOrderOne

end StructuralRamsey.Girth
