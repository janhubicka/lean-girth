import Girth.TrainTopParentBridge
import Girth.AttachmentGeometry
import Girth.TrainSharedOldACarrierCoreEmbedding

/-!
# Pointwise shared A-edge incidence in the actual active relational attachment

A universal top parent can be handled without a next system-girth
coordinate only if a vertex x of a standard copy meeting the witness
core is on a *genuine common support edge* through x.

Here the gluing set is the TRUE active subsystem: the union of all
projected old A-copy carriers. We prove the exact missing incidence
at the physical A-support level, including an actual core A-carrier
with exactly the same physical image as the shared old A-carrier.

The induced old/core wagon ancestor of this physical support edge is
not yet connected to the abstract generated-tag parameter bridge.
That final identification is deliberately left as a separate task.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P Old Core I : Type v}

/-- A shared core/standard vertex in the genuine nontrivial
active attachment lies on the images of a genuine shared OLD
A-support edge and a genuine CORE A-support edge. Their physical
image sets are equal, not merely overlapping at the vertex.

The proof does NOT require all ambient old edges to be covered by
designated target copies, nor the witness system-Girth bound. -/
theorem activeAttached_coreStandard_pointwise_sharedAEdge
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding
      (B.toRelStructure.induce (activeCarrier A B α)) D)
    (i : I)
    (z : RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I))
    (hzStandard : z ∈ copyCarrier
      (RelStructure.Attachment.copyEmbedding
        B.toRelStructure (activeCarrier A B α) D f i))
    (hzCore : z ∈ copyCarrier
      (RelStructure.Attachment.coreEmbedding
        B.toRelStructure (activeCarrier A B α) D f)) :
    ∃ T : SharedOldACarrierEdge
        A B.toRelStructure (activeCarrier A B α),
      ∃ U : OldACarrierEdge A D,
        z ∈
          ((fun x : Old =>
              (RelStructure.Attachment.copyEmbedding B.toRelStructure
                (activeCarrier A B α) D f i) x) '' T.1.1) ∧
        z ∈
          ((fun y : Core =>
              (RelStructure.Attachment.coreEmbedding B.toRelStructure
                (activeCarrier A B α) D f) y) '' U.1) ∧
        ((fun x : Old =>
              (RelStructure.Attachment.copyEmbedding B.toRelStructure
                (activeCarrier A B α) D f i) x) '' T.1.1) =
          ((fun y : Core =>
              (RelStructure.Attachment.coreEmbedding B.toRelStructure
                (activeCarrier A B α) D f) y) '' U.1) := by
  let S : Set Old := activeCarrier A B α
  have hInter :
      z ∈ copyCarrier
        (RelStructure.Attachment.copyEmbedding
          B.toRelStructure S D f i) ∩
        copyCarrier
          (RelStructure.Attachment.coreEmbedding
            B.toRelStructure S D f) :=
    ⟨hzStandard, hzCore⟩
  rw [attachment_copy_core_intersection
    B.toRelStructure S D f i] at hInter
  rcases hInter with ⟨y, hy⟩
  change
    (RelStructure.Attachment.coreEmbedding
      B.toRelStructure S D f) (f i y) = z at hy
  obtain ⟨T, hT⟩ :=
    activeCarrier_vertex_has_sharedOldAEdge A B α y.1 y.2
  have hzOld :
      z ∈ ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding
          B.toRelStructure S D f i) x) '' T.1.1) := by
    refine ⟨y.1, hT, ?_⟩
    exact
      (RelStructure.Attachment.copy_extends
        B.toRelStructure S D f i y).trans hy
  let U : OldACarrierEdge A D :=
    sharedOldACarrierCoreMap A B.toRelStructure S D f i T
  have hImages :
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding
          B.toRelStructure S D f i) x) '' T.1.1) =
      ((fun y : Core =>
        (RelStructure.Attachment.coreEmbedding
          B.toRelStructure S D f) y) '' U.1) :=
    sharedOldACarrierCoreMap_image A B.toRelStructure S D f i T
  refine ⟨T, U, hzOld, ?_, hImages⟩
  exact hImages ▸ hzOld

end StructuralRamsey.Girth
