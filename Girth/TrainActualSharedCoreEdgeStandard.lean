import Girth.TrainActualCopyLocalCoreIncidence
import Girth.TrainActualPhysicalEdgeCarrierEval

/-!
# Actual shared core edges are physically contained in their own standard

The shared witness's edges are not merely abstract core supports.
The actual physical image of a shared edge from copy i has its whole
carrier inside standard i. This is a direct core/carrier compatibility
lemma and requires no wagon linearity or cycle-replacement hypothesis.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA Old Core I : Type v}

/-- An actual shared A-support edge chosen from witness copy i lies
physically inside its attached standard. Carrier inclusion, not an
equality of edge labels, is the needed conclusion. -/
theorem actualSharedCoreEdge_carrier_subset_standard
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L Old) (S : Set Old)
    (R : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) R)
    (i : I) (s : SharedOldACarrierEdge A B S) :
    (actualAPictureEdgeEquiv A hA B S R f
      (physicalCoreEdge (sharedOldACarrierInclusion A B S) I
        (sharedOldACarrierCoreEmbedding A B S R f i s))).1 ⊆
    copyCarrier (RelStructure.Attachment.copyEmbedding B S R f i) := by
  rw [actualAPictureEdgeEquiv_core_carrier]
  intro z hz
  change z ∈ ((fun y : Core =>
    RelStructure.Attachment.coreEmbedding B S R f y) ''
    (sharedOldACarrierCoreEmbedding A B S R f i s).1) at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨t, ht⟩ :=
    sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
      A B S R f i s hy
  refine ⟨t.val, ?_⟩
  simpa only [ht] using
    (RelStructure.Attachment.copy_extends B S R f i t)

end StructuralRamsey.Girth
