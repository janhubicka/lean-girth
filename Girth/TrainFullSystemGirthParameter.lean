import Girth.TrainSimultaneousSupreme
import Girth.TrainActualSupportParameterTransport

/-!
# Circulation: full system girth supplies the actual A-support parameter

The previous physical parameter theorem required an exact order-one
bridge premise. The new global simultaneous-replacement cycle syntax
proves that the manuscript-style full system-girth hypothesis yields it.

At every non-top parent cut, assuming the witnessed pretrain has full
system girth above some q >= 1, the generated train on the ACTUAL
attached A-support edge family satisfies the same sibling parameter.

The old and core parameter hypotheses, reflection on shared subsystem
trains, and nonempty active shared support remain explicit.
This is a circulation step, not an appendix or higher-order transfer.
-/

namespace StructuralRamsey.Girth

universe u v
open StructuralRamsey.RelStructure
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

namespace OrderOneData

/-- A system-girth bound at any cutoff at least one implies the
exact mixed two-occurrence bound: restrict its cycle budget to one. -/
theorem bound_of_fullSystemGirth_ge_one
    {V E J Q : Type v} (D : OrderOneData V E J Q)
    (q : ℕ) (hq : 1 ≤ q)
    (h : D.FullSystemGirthGT q) : D.Bound := by
  apply D.orderOneBound_of_fullSystemGirth
  refine ⟨h.1, ?_⟩
  intro n C hAccept hSmall
  exact h.2 n C hAccept (by omega)

end OrderOneData

/-- The full circulation supreme-cycle condition in the witness,
with cutoff at least one, establishes the sibling-intersection
parameter on genuine A-support wagon quotients of the free attachment.
In particular NO independent bridge assumption is needed. -/
theorem activeAttached_actualASupport_parentBound_of_fullSystemGirth
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
    (q : ℕ) (hq : 1 ≤ q)
    (hFull :
      (sharedWitnessOrderOneData coreTrain ν
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f)).FullSystemGirthGT q) :
    TrainParentIntersectionBound
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).wagonClassCarrier
          (fun e : ActualAttachedAEdge A B.toRelStructure
            (activeCarrier A B α) D f => e.1) μ)
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).wagonParent μ ν hμν) allowed := by
  exact activeAttached_actualASupport_parentBound_of_orderOne
    A hA B α D f oldTrain coreTrain μ ν hμν
    hShared hRel allowed hOld hCore
    (OrderOneData.bound_of_fullSystemGirth_ge_one
      (sharedWitnessOrderOneData coreTrain ν
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f))
      q hq hFull)

end StructuralRamsey.Girth
