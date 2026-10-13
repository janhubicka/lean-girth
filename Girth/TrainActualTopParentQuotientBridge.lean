import Girth.TrainTopParentSharedQuotientComposite
import Girth.TrainActualActiveCoreStandardBridge

/-!
# Actual active relational top-parent two-source bridge

The abstract top-parent quotient bridge has an explicit pointwise
physical shared-edge premise. We discharge it for the *true active*
gluing subsystem of a relational partite picture, using genuine
A-support carrier sets rather than raw A-embedding labels.

This identifies actual OLD and CORE quotient child wagon carriers,
their parent maps to the universal top class, and their contact
map. It neither constructs the global generated attached train tag
equivalence nor derives interior parent bridges from system-girth:
these are separate obligations.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P Old Core I : Type v}

/-- The actual physical vertex carrier of an old support edge
in an indexed attached standard picture. -/
def attachedOldAEdgeCarrier
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (e : OldACarrierEdge A B) :
    Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
  (fun x : Old =>
    (RelStructure.Attachment.copyEmbedding B S D f i) x) '' e.1

/-- The actual physical vertex carrier of a core support edge. -/
def attachedCoreAEdgeCarrier
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (e : OldACarrierEdge A D) :
    Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
  (fun y : Core =>
    (RelStructure.Attachment.coreEmbedding B S D f) y) '' e.1

/-- A genuine shared old A-support edge and its actual core image
have exactly the same physical edge carrier. -/
theorem attachedSharedAEdgeCarrier_eq
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (s : SharedOldACarrierEdge A B S) :
    attachedOldAEdgeCarrier A B S D f i
        (sharedOldACarrierInclusion A B S s) =
      attachedCoreAEdgeCarrier A B S D f
        (sharedOldACarrierCoreEmbedding A B S D f i s) := by
  exact sharedOldACarrierCoreMap_image A B S D f i s

/-- Pointwise bridge in the actual relational active attachment:
an old A-support edge touching a core vertex in standard picture i
can be replaced at that vertex by a GENUINELY SHARED old A-support
edge (whose carrier is wholly inside the true active gluing set).

This requires no Ramsey arrow, ambient A-edge coverage or
system-girth, but it would be false for arbitrary gluing sets with
isolated old vertices. -/
theorem activeAttached_sharedOldAEdge_at_coreVertex
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding
      (B.toRelStructure.induce (activeCarrier A B α)) D)
    (i : I) (e : OldACarrierEdge A B.toRelStructure)
    (z : RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I))
    (hzCore : z ∈ copyCarrier
      (RelStructure.Attachment.coreEmbedding
        B.toRelStructure (activeCarrier A B α) D f))
    (hzOld : z ∈ attachedOldAEdgeCarrier
      A B.toRelStructure (activeCarrier A B α) D f i e) :
    ∃ s : SharedOldACarrierEdge A B.toRelStructure
        (activeCarrier A B α),
      z ∈ attachedOldAEdgeCarrier
        A B.toRelStructure (activeCarrier A B α) D f i
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) s) := by
  have hzStandard : z ∈ copyCarrier
      (RelStructure.Attachment.copyEmbedding
        B.toRelStructure (activeCarrier A B α) D f i) := by
    rcases hzOld with ⟨y, _hy, hzy⟩
    exact ⟨y, hzy⟩
  obtain ⟨s, _u, hOld, _hCore, _hEq⟩ :=
    activeAttached_coreStandard_pointwise_sharedAEdge
      A B α D f i z hzStandard hzCore
  exact ⟨s, hOld⟩

/-- The top-parent two-source bridge on GENUINE A-support wagon
quotients of the actual relational attachment.

At the selected child cut the shared-subsystem train embeddings must
preserve AND reflect equivalence. The physical core/standard
intersection geometry and pointwise shared A-support coverage are
proved internally, rather than postulated as an extra witness lemma.
The old/core quotient parent maps are the actual universal TOP maps.

This is not yet the full generated train parent-parameter theorem:
its identification of these quotient classes with all generated
attached wagon tags, and the interior order-one witness bridges,
remain separate formalization obligations. -/
theorem activeAttached_topParent_twoSourceBridge
    {m : ℕ}
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding
      (B.toRelStructure.induce (activeCarrier A B α)) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B.toRelStructure) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (μ : Fin (m + 1))
    (hμtop : μ ≤ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hRel : ∀ (i : I)
      (s t : SharedOldACarrierEdge A B.toRelStructure
        (activeCarrier A B α)),
      oldTrain.rel μ
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) s)
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) t) ↔
      coreTrain.rel μ
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i s)
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i t))
    (allowed : Set (RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I))) :
    ParentCoreTwoSourceBridge
      (fun i => oldTrain.wagonClassCarrier
        (attachedOldAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f i) μ)
      (oldTrain.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop)
      (coreTrain.wagonClassCarrier
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f) μ)
      (coreTrain.wagonParent μ ⟨m, Nat.lt_succ_self m⟩ hμtop)
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel oldTrain μ
          (fun _ : I => sharedOldACarrierInclusion
            A B.toRelStructure (activeCarrier A B α)))
        (oldSharedWagonLabel coreTrain μ
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D f))))
      (wagonContactGlue (wagonSharedEdgeContact
        (oldSharedWagonLabel oldTrain ⟨m, Nat.lt_succ_self m⟩
          (fun _ : I => sharedOldACarrierInclusion
            A B.toRelStructure (activeCarrier A B α)))
        (oldSharedWagonLabel coreTrain ⟨m, Nat.lt_succ_self m⟩
          (sharedOldACarrierCoreEmbedding A B.toRelStructure
            (activeCarrier A B α) D f))))
      (copyCarrier (RelStructure.Attachment.coreEmbedding
        B.toRelStructure (activeCarrier A B α) D f))
      allowed := by
  apply topParent_twoSourceBridge_of_sharedQuotientCoverage
    oldTrain coreTrain μ hμtop
    (fun _ : I => sharedOldACarrierInclusion
      A B.toRelStructure (activeCarrier A B α))
    (sharedOldACarrierCoreEmbedding A B.toRelStructure
      (activeCarrier A B α) D f)
    hRel
    (attachedOldAEdgeCarrier A B.toRelStructure
      (activeCarrier A B α) D f)
    (attachedCoreAEdgeCarrier A B.toRelStructure
      (activeCarrier A B α) D f)
    (by
      intro i s
      exact attachedSharedAEdgeCarrier_eq A B.toRelStructure
        (activeCarrier A B α) D f i s)
    (copyCarrier (RelStructure.Attachment.coreEmbedding
      B.toRelStructure (activeCarrier A B α) D f))
    allowed
  intro i e z hzCore hzOld
  exact activeAttached_sharedOldAEdge_at_coreVertex
    A B α D f i e z hzCore hzOld

end StructuralRamsey.Girth
