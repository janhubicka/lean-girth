import Girth.TrainActualActiveCoreStandardBridge
import Girth.TrainSharedOldACarrierCoreEmbedding
import Girth.TrainInteriorParentQuotientBridge

/-!
# Active gluing-copy vertices are supported by genuine shared core edges

The selected-picture vertex cut theorem locates a core vertex y in
the actual embedded gluing copy f i. To make its owner a designated
label in the witness big cycle, one needs more: y is incident with
an actual SHARED A-support edge of that same copy. This holds because
the active subsystem is A-generated; it is not a free hypothesis
about arbitrary copy carriers.

This lemma proves precisely the resulting membership in the real
core-valued sharedWitnessOrderOneData. It does not assert that all
output-copy vertices are shared, or construct the witness cycle.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- Every vertex of an actual embedded active subsystem gluing copy
is covered by one genuine shared core A-support edge of that copy. -/
theorem activeCoreWitness_vertex_mem_sharedCopy
    {L : RelLanguage.{u}} {UA P X Y I : Type v}
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) (i : I)
    (y : Y) (hy : y ∈ copyCarrier (f i)) :
    y ∈ (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C α) R f)
      (Subtype.val : OldACarrierEdge A R → Set Y)).copyCarrier i := by
  let S := activeCarrier A C α
  let core := RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
  let std := RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i
  obtain ⟨x, hxy⟩ := hy
  obtain ⟨s, hs⟩ :=
    activeCarrier_vertex_has_sharedOldAEdge A C α x.1 x.2
  refine ⟨s, ?_⟩
  -- Expose the actual core carrier, rather than leaving the
  -- shared-edge embedding subtype coercion opaque to rewriting.
  change y ∈ (sharedOldACarrierCoreMap
    A C.toRelStructure S R f i s).1
  have hImage :=
    sharedOldACarrierCoreMap_image A C.toRelStructure S R f i s
  have hCoreImage :
      (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f) y ∈
        (fun z : Y =>
          (RelStructure.Attachment.coreEmbedding C.toRelStructure S R f) z) ''
        (sharedOldACarrierCoreMap
          A C.toRelStructure S R f i s).1 := by
    rw [← hImage]
    refine ⟨x.1, hs, ?_⟩
    calc
      std x.1 = core (f i x) :=
        RelStructure.Attachment.copy_extends C.toRelStructure S R f i x
      _ = core y := congrArg core hxy
  obtain ⟨z, hz, hzEq⟩ := hCoreImage
  have hzy : z = y := core.injective hzEq
  simpa [hzy] using hz

end StructuralRamsey.Girth
