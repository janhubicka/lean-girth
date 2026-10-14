import Girth.TrainActualTopParentQuotientBridge
import Girth.TrainInteriorParentQuotientBridge
import Girth.AttachmentGeometry

/-!
# Discharge source carrier geometry in actual relational attachment

Every old wagon's full carrier stays in its indexed standard copy;
every core wagon's full carrier stays in the core; distinct standard
copies meet only in that core. These conclusions apply to actual wagon
quotient classes, not only to representative edges. They require no
system-girth or Ramsey premise and do not collapse equal carriers.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {UA Old Core I : Type v}

/-- Any old source wagon, at any level, has its complete physical
vertex carrier inside its indexed standard picture. -/
theorem attachedOldAWagon_carrier_subset_copy
    {m : ℕ}
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A B) m)
    (μ : Fin (m + 1))
    (i : I) (u : Quotient (T.wagonSetoid μ)) :
    T.wagonClassCarrier
      (attachedOldAEdgeCarrier A B S D f i) μ u ⊆
    copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) := by
  intro x hx
  obtain ⟨e, _he, hxe⟩ :=
    T.exists_incident_representative
      (attachedOldAEdgeCarrier A B S D f i) μ u x hx
  rcases hxe with ⟨y, _hy, hxy⟩
  exact ⟨y, hxy⟩

/-- Any core source wagon has its entire physical carrier inside
the actual core of the attached structure. -/
theorem attachedCoreAWagon_carrier_subset_core
    {m : ℕ}
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A D) m)
    (μ : Fin (m + 1))
    (c : Quotient (T.wagonSetoid μ)) :
    T.wagonClassCarrier
      (attachedCoreAEdgeCarrier A B S D f) μ c ⊆
    copyCarrier (RelStructure.Attachment.coreEmbedding B S D f) := by
  intro x hx
  obtain ⟨e, _he, hxe⟩ :=
    T.exists_incident_representative
      (attachedCoreAEdgeCarrier A B S D f) μ c x hx
  rcases hxe with ⟨y, _hy, hxy⟩
  exact ⟨y, hxy⟩

/-- The off-core standard index is unique even after replacing
individual edges by their complete generated-source wagon carriers. -/
theorem attachedOldAWagon_offCore_index_unique
    {m : ℕ}
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (T : EdgeTrainLevels (OldACarrierEdge A B) m)
    (μ : Fin (m + 1))
    (i j : I) (u v : Quotient (T.wagonSetoid μ))
    (x : RelStructure.Attachment.Vertex S (W := Core) (I := I))
    (hxOutside : x ∉
      copyCarrier (RelStructure.Attachment.coreEmbedding B S D f))
    (hxI : x ∈ T.wagonClassCarrier
      (attachedOldAEdgeCarrier A B S D f i) μ u)
    (hxJ : x ∈ T.wagonClassCarrier
      (attachedOldAEdgeCarrier A B S D f j) μ v) :
    i = j := by
  by_contra hij
  have hInI : x ∈ copyCarrier
      (RelStructure.Attachment.copyEmbedding B S D f i) :=
    attachedOldAWagon_carrier_subset_copy
      A B S D f T μ i u hxI
  have hInJ : x ∈ copyCarrier
      (RelStructure.Attachment.copyEmbedding B S D f j) :=
    attachedOldAWagon_carrier_subset_copy
      A B S D f T μ j v hxJ
  exact hxOutside
    (attachment_copy_copy_intersection_subset_core B S D f hij
      ⟨hInI, hInJ⟩)

end StructuralRamsey.Girth
