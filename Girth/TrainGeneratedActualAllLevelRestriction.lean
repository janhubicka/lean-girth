import Girth.TrainGeneratedActualASupportTrain
import Girth.TrainPhysicalPictureAllLevelRestriction

/-!
# Exact generated wagon relations on the real A-support hypergraph

The underlying REAL A-copy support edges of a free attachment are
canonically bijective to the physical picture edge pushout. The
physical picture already has a generated nested train at every cut.

If the original standard/core train embeddings preserve AND reflect
wagon equivalence on their real shared A-support edges, the generated
relations restrict EXACTLY to each old standard copy. For the core,
preservation alone suffices. These are statements directly on the
genuine relational A-support carrier type: no duplicate embedding
labels, designated-copy coverage or edge pruning are used.

This closes the generated equivalence restriction calculation,
conditional only on the true shared-subsystem train embedding
interface and the nonempty shared-edge hypothesis. Allowed-part
intersection parameters, A1--A3 system-Girth and the recursive
Ramsey witness remain unverified.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- At EVERY level the generated train on the genuine physical
A-support edges restricts exactly to the old standard picture's
wagon equivalence, provided the genuine shared train embedding
preserves and reflects wagon equivalences. -/
theorem generatedActualASupportTrain_restrict_standard
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (hRel : ∀ (μ : Fin (m + 1)) (i : I)
       (s t : SharedOldACarrierEdge A B S),
      oldTrain.rel μ
          (sharedOldACarrierInclusion A B S s)
          (sharedOldACarrierInclusion A B S t) ↔
        coreTrain.rel μ
          (sharedOldACarrierCoreEmbedding A B S D f i s)
          (sharedOldACarrierCoreEmbedding A B S D f i t))
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S))
    (μ : Fin (m + 1))
    (i : I) (a b : OldACarrierEdge A B) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).rel μ
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i a))
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i b))
      ↔ oldTrain.rel μ a b := by
  have hPhysical :=
    physicalPictureGeneratedTrain_restrict_standard
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hRel hShared μ i a b
  have hActual :=
    generatedActualASupportTrain_rel_iff
      A hA B S D f oldTrain coreTrain hShared μ
      (physicalStandardEdge
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f) i a)
      (physicalStandardEdge
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f) i b)
  exact hActual.trans hPhysical

/-- At EVERY level the actual generated picture train restricts to
the original core witness train, already under preservation of
the genuine shared-subsystem edge-equivalence relations. -/
theorem generatedActualASupportTrain_restrict_core
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (hPreserve : ∀ (μ : Fin (m + 1)) (i : I)
       (s t : SharedOldACarrierEdge A B S),
      oldTrain.rel μ
          (sharedOldACarrierInclusion A B S s)
          (sharedOldACarrierInclusion A B S t) →
        coreTrain.rel μ
          (sharedOldACarrierCoreEmbedding A B S D f i s)
          (sharedOldACarrierCoreEmbedding A B S D f i t))
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S))
    (μ : Fin (m + 1))
    (a b : OldACarrierEdge A D) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).rel μ
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalCoreEdge
          (sharedOldACarrierInclusion A B S) I a))
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalCoreEdge
          (sharedOldACarrierInclusion A B S) I b))
      ↔ coreTrain.rel μ a b := by
  have hPhysical :=
    physicalPictureGeneratedTrain_restrict_core
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hPreserve hShared μ a b
  have hActual :=
    generatedActualASupportTrain_rel_iff
      A hA B S D f oldTrain coreTrain hShared μ
      (physicalCoreEdge (sharedOldACarrierInclusion A B S) I a)
      (physicalCoreEdge (sharedOldACarrierInclusion A B S) I b)
  exact hActual.trans hPhysical

end StructuralRamsey.Girth
