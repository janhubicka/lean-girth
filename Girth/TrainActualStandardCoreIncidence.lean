import Girth.TrainStandardCoreWagonIncidence

/-!
# Circulation: standard/core contact in the actual relational A-support

The standard/core incidence theorem on the physical edge pushout
transports through the actual support-edge equivalence. Its shared
core edge is contained in the particular witness copy Q_i.

The hypotheses hShared and hRel remain explicit, as does the
source incidence in the generated train. This is NOT a proof of
the actual minimum-segmentation reduct or its A1--A3 properties.
No appendix is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Actual A-support standard/core boundary: a core witness edge
in the same wagon as the given standard edge can be reached by
a shared edge of the old wagon whose core carrier lies in Q_i. -/
theorem generatedActualASupportTrain_standard_core_copy_local_incidence
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
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
    (μ : Fin (m + 1)) (i : I)
    (a : OldACarrierEdge A B) (b : OldACarrierEdge A D)
    (hSame :
      (generatedActualASupportTrain A hA B S D f
        oldTrain coreTrain hShared).rel μ
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i a))
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalCoreEdge
          (sharedOldACarrierInclusion A B S) I b))) :
    ∃ s : SharedOldACarrierEdge A B S,
      oldTrain.rel μ (sharedOldACarrierInclusion A B S s) a ∧
      coreTrain.rel μ
        (sharedOldACarrierCoreEmbedding A B S D f i s) b ∧
      (sharedOldACarrierCoreEmbedding A B S D f i s).1 ⊆
        Set.range (f i) := by
  have hPhysical :
      (physicalPictureGeneratedTrain
        oldTrain coreTrain
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f)
        hShared).rel μ
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i a)
        (physicalCoreEdge
          (sharedOldACarrierInclusion A B S) I b) :=
    (physicalPictureGeneratedTrain_rel_iff
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hShared μ _ _).mpr
        ((generatedActualASupportTrain_rel_iff
          A hA B S D f oldTrain coreTrain hShared μ _ _).mp hSame)
  obtain ⟨s, hsOld, hsCore⟩ :=
    PhysicalWagonModel.standard_core_wagon_incidence_witness
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hShared hRel μ i a b hPhysical
  exact ⟨s, hsOld, hsCore,
    sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
      A B S D f i s⟩

end StructuralRamsey.Girth
