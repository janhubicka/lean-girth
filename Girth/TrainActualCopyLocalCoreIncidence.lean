import Girth.TrainSharedOldACarrierCoreEmbedding

/-!
# Circulation: shared A-support is local to the prescribed witness copy

The core ancestor of a genuinely shared A-support carrier reached from
standard i is contained in the particular copy Q_i = range (f i) of
the gluing subsystem, not merely in the ambient witness H.

This is an incidence lemma; it does not construct a segmented reduct.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The core carrier of a genuine shared A-edge lies inside the
specific embedded gluing copy indexed by i. -/
theorem sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I)
    (T : SharedOldACarrierEdge A B S) :
    (sharedOldACarrierCoreEmbedding A B S D f i T).1 ⊆
      Set.range (f i) := by
  let core := RelStructure.Attachment.coreEmbedding B S D f
  let std := RelStructure.Attachment.copyEmbedding B S D f i
  intro y hy
  have hOld :
      core y ∈ (fun x : Old => std x) '' T.1.1 := by
    rw [sharedOldACarrierCoreMap_image A B S D f i T]
    exact ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hOld
  have hxS : x ∈ S := T.2 hx
  refine ⟨⟨x, hxS⟩, ?_⟩
  apply core.injective
  calc
    core (f i ⟨x, hxS⟩) = std x :=
      (RelStructure.Attachment.copy_extends B S D f i ⟨x, hxS⟩).symm
    _ = core y := hxy

end StructuralRamsey.Girth
