import Girth.TrainActualPhysicalEdgeCarrierEval
import Girth.TrainActualPhysicalParameterComposite
import Girth.TrainGeneratedActualASupportTrain
import Girth.TrainWagonQuotientTransport

/-!
# Generated parameters on actual relational A-support wagon quotients

The physical edge-pushout equivalence is carrier preserving on both
core and standard edges, including genuine shared old A-support edges.
Therefore transport the already proved physical generated sibling
bound to the actual attached A-support hypergraph, without assuming
that distinct quotient labels have different vertex carriers.

The source-train parameter assumptions and the exact parent-cut
order-one witness bound remain explicit. This does not prove the
full A1--A3 system-Girth preservation or recursive Ramsey theorem.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- On the true active relational A-support attachment, the generated
actual physical A-support train preserves the allowed sibling
intersection parameter at a selected child/parent cut, assuming
the original parameters, shared-reflection, and order-one bound. -/
theorem activeAttached_actualASupport_parentBound_of_orderOne
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
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
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).
        wagonClassCarrier
          (fun e : ActualAttachedAEdge A B.toRelStructure
            (activeCarrier A B α) D f => e.1) μ)
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).
        wagonParent μ ν hμν) allowed := by
  let S := activeCarrier A B α
  let ϕ := actualAPictureEdgeEquiv A hA B.toRelStructure S D f
  let T := physicalPictureGeneratedTrain oldTrain coreTrain
    (sharedOldACarrierInclusion A B.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A B.toRelStructure S D f)
    hShared
  have hPhysical : TrainParentIntersectionBound
      (T.wagonClassCarrier
        (fun e : ActualAPicturePushoutEdge A B.toRelStructure S D I =>
          (ϕ e).1) μ)
      (T.wagonParent μ ν hμν) allowed := by
    apply activeAttached_physicalGenerated_parentBound_of_orderOne
      A B α D f oldTrain coreTrain μ ν hμν hShared hRel
      (fun e : ActualAPicturePushoutEdge A B.toRelStructure S D I =>
        (ϕ e).1)
    · intro b
      exact actualAPictureEdgeEquiv_core_carrier
        A hA B.toRelStructure S D f b
    · intro i e
      exact actualAPictureEdgeEquiv_standard_carrier
        A hA B.toRelStructure S D f i e
    · exact allowed
    · exact hOld
    · exact hCore
    · exact hOrderOne
  exact T.wagonTransport_parentIntersectionBound ϕ
    (fun e : ActualAPicturePushoutEdge A B.toRelStructure S D I =>
      (ϕ e).1)
    (fun e : ActualAttachedAEdge A B.toRelStructure S D f => e.1)
    (by intro e; rfl)
    μ ν hμν allowed hPhysical

end StructuralRamsey.Girth
