import Girth.TrainSharedOldACarrierCoreEmbedding
import Girth.TrainCrossStandardCoreIncidence

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


/-- A cross-standard output wagon comes with genuinely shared old
incidence edges on both sides whose core ancestors belong to the
specified embedded witness copies, and carry the same core wagon tag.

This theorem does not obtain the boundary edges of a segmented cycle:
those need to be extracted from the actual labelled occurrences.
Both the shared-support existence and train-reflection hypotheses
remain explicit. -/
theorem cross_standard_wagon_copy_local_core_incidence
    {m : ℕ}
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S))
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      oldTrain.rel κ
        (sharedOldACarrierInclusion A B S s)
        (sharedOldACarrierInclusion A B S t) ↔
      coreTrain.rel κ
        (sharedOldACarrierCoreEmbedding A B S D f i s)
        (sharedOldACarrierCoreEmbedding A B S D f i t))
    (μ : Fin (m + 1)) (i j : I) (hij : i ≠ j)
    (a b : OldACarrierEdge A B)
    (hSame :
      (physicalPictureGeneratedTrain oldTrain coreTrain
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f) hShared).rel μ
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i a)
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) j b)) :
    ∃ (c : Quotient (coreTrain.wagonSetoid μ))
      (s t : SharedOldACarrierEdge A B S),
      oldTrain.rel μ (sharedOldACarrierInclusion A B S s) a ∧
      oldTrain.rel μ (sharedOldACarrierInclusion A B S t) b ∧
      Quotient.mk (coreTrain.wagonSetoid μ)
        (sharedOldACarrierCoreEmbedding A B S D f i s) = c ∧
      Quotient.mk (coreTrain.wagonSetoid μ)
        (sharedOldACarrierCoreEmbedding A B S D f j t) = c ∧
      (sharedOldACarrierCoreEmbedding A B S D f i s).1 ⊆
        Set.range (f i) ∧
      (sharedOldACarrierCoreEmbedding A B S D f j t).1 ⊆
        Set.range (f j) := by
  obtain ⟨c, s, t, hs, ht, hsc, htc⟩ :=
    PhysicalWagonModel.cross_standard_wagon_two_core_incidence_witnesses
      oldTrain coreTrain (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hShared hRel μ i j hij a b hSame
  exact ⟨c, s, t, hs, ht, hsc, htc,
    sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
      A B S D f i s,
    sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
      A B S D f j t⟩

end StructuralRamsey.Girth
