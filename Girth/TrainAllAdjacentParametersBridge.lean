import Girth.TrainAllAdjacentParameterPreservation

/-!
# Circulation: exact two-source bridge hypothesis for all parameters

The original all-adjacent theorem was checked under the stronger
full system-girth condition at interior parent cuts. The manuscript
parameter lemma needs only actual order-one two-source bridges:
two distinct labels containing x and meeting the same witness wagon
must each have an edge of that wagon through x.

The existing exact equivalence
OrderOneData.bound_iff_both_bridges lets us express precisely that
hypothesis as Bound at each interior cut. The existing actual
relational parent parameter bridge proves the interior case; genuine
active shared-edge coverage handles the universal top, without an
extra cycle coordinate.

This file formalizes the exact one-step parameter lemma and leaves
higher-order cycle transfer, Ramsey recursion and appendix untouched.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}

/-- All adjacent sibling intersection parameters are preserved under
the EXACT two-source order-one bridge hypothesis at each interior cut.
The universal top is handled by actual pointwise shared-edge coverage,
with no nonexistent next system-girth coordinate.

The order-one bound here is equivalent to the manuscript's pairwise
two-source bridge property (OrderOneData.bound_iff_both_bridges).
This strengthens the checked all-adjacent result without requiring
the full higher-order system-girth condition. -/
theorem activeAttached_actualASupport_allAdjacentParameters_of_orderOne
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
    (allowed : Fin (m + 1) → Set
      (RelStructure.Attachment.Vertex
        (activeCarrier A B α) (W := Core) (I := I)))
    (hOld : ∀ i : I,
      oldTrain.AdjacentParameters
        (attachedOldAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f i) allowed)
    (hCore : coreTrain.AdjacentParameters
      (attachedCoreAEdgeCarrier A B.toRelStructure
        (activeCarrier A B α) D f) allowed)
    (hOrderOne : ∀ ν : Fin (m + 1), 0 < ν.val → ν.val < m →
      (sharedWitnessOrderOneData coreTrain ν
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f)
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f)).Bound) :
    (generatedActualASupportTrain A hA B.toRelStructure
      (activeCarrier A B α) D f oldTrain coreTrain hShared).AdjacentParameters
        (fun e : ActualAttachedAEdge A B.toRelStructure
          (activeCarrier A B α) D f => e.1)
        allowed := by
  intro μ ν hμν hSucc
  have hOldAt : ∀ i : I,
      TrainParentIntersectionBound
        (oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B.toRelStructure
            (activeCarrier A B α) D f i) μ)
        (oldTrain.wagonParent μ ν hμν) (allowed ν) :=
    fun i => hOld i μ ν hμν hSucc
  have hCoreAt :
      TrainParentIntersectionBound
        (coreTrain.wagonClassCarrier
          (attachedCoreAEdgeCarrier A B.toRelStructure
            (activeCarrier A B α) D f) μ)
        (coreTrain.wagonParent μ ν hμν) (allowed ν) :=
    hCore μ ν hμν hSucc
  by_cases hTop : ν.val = m
  · have hνTop : ν = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) :=
      Fin.ext hTop
    exact activeAttached_actualASupport_parentBound_at_top
      A hA B α D f oldTrain coreTrain μ ν hμν
      hνTop hShared hRel (allowed ν) hOldAt hCoreAt
  · have hInterior : ν.val < m := by omega
    exact activeAttached_actualASupport_parentBound_of_orderOne
      A hA B α D f oldTrain coreTrain μ ν hμν
      hShared hRel (allowed ν) hOldAt hCoreAt
      (hOrderOne ν (by omega) hInterior)

end StructuralRamsey.Girth
