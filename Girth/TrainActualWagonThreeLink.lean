import Girth.TrainWagonThreeLink
import Girth.TrainGeneratedActualASupportTrain

/-!
# Circulation: the three-link generated quotient on actual A-support edges

The physical picture quotient already has a checked short generator
chain: an old-standard wagon edge is equivalent to a shared old edge,
whose core image is core-wagon equivalent to a second shared image,
which is old-standard wagon equivalent to a second outer edge.

This file transports that EXACT relation to the genuine physical
A-copy carrier family in a relational attachment, using the checked
old/core edge pushout equivalence. No new geometric hypothesis,
duplicate raw embedding tag or accidental equality of vertex carriers
is introduced. It is the actual-structure quotient part of the
edge-block two-standard argument; it does NOT by itself prove that
a chosen long witness edge and old block edge have the same old wagon.

Only the circulation manuscript is addressed. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- In an actual relational attachment, the generated wagon relation
connects any two old standard A-support edges whenever each lies in
the wagon of a genuinely shared edge and those two shared core images
lie in a single core wagon. The conclusion is on the real physical
A-support carriers, not merely the disjoint source presentation. -/
theorem generatedActualASupportTrain_three_link
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
    (μ : Fin (m + 1)) (i j : I)
    (a b : OldACarrierEdge A B)
    (s t : SharedOldACarrierEdge A B S)
    (hOldA : oldTrain.rel μ a
      (sharedOldACarrierInclusion A B S s))
    (hCore : coreTrain.rel μ
      (sharedOldACarrierCoreEmbedding A B S D f i s)
      (sharedOldACarrierCoreEmbedding A B S D f j t))
    (hOldB : oldTrain.rel μ
      (sharedOldACarrierInclusion A B S t) b) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).rel μ
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i a))
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) j b)) := by
  let inOld := sharedOldACarrierInclusion A B S
  let inCore := sharedOldACarrierCoreEmbedding A B S D f
  have hPicture :=
    physicalPictureGeneratedTrain_three_link oldTrain coreTrain
      inOld inCore hShared μ i j a b s t hOldA hCore hOldB
  have hGenerated :
      TrainEdgeGenerated
        (physicalPictureCutStep oldTrain coreTrain μ inOld inCore)
        (physicalStandardEdge inOld inCore i a)
        (physicalStandardEdge inOld inCore j b) :=
    (physicalPictureGeneratedTrain_rel_iff
      oldTrain coreTrain inOld inCore hShared μ _ _).mp hPicture
  exact (generatedActualASupportTrain_rel_iff
    A hA B S D f oldTrain coreTrain hShared μ _ _).mpr hGenerated

end StructuralRamsey.Girth
