import Girth.TrainPhysicalPictureGeneratedTrain
import Girth.TrainEdgeEquivalenceTransport
import Girth.TrainActualPhysicalAEdgePushout

/-!
# Actual generated picture train on the full relational A-support family

Start with old/core trains whose physical edge labels are genuine
A-copy carriers. The canonical old shared-A-edge inclusion and
injective shared-to-core map supply the concrete physical picture
edge pushout. Its generated wagon hierarchy is nested with equality
at the bottom and universal relation at the top, provided every
attached standard picture has a real shared support edge.

The checked physical A-support edge-pushout bijection transports
this WHOLE hierarchy onto the actual A-support edge family of
the free relational attachment, without losing any support edges
or conflating duplicate raw A-embeddings.

This is a generated hierarchy of EQUIVALENCE RELATIONS. The sibling
part-parameter restrictions and acceptable-cycle system-Girth
A1--A3 remain genuine separate proof obligations.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The full generated wagon hierarchy on genuine physical
A-support edges of the actual relational attachment.

The only additional contact hypothesis is that each attached
standard picture has at least one genuinely shared A-support edge. -/
noncomputable def generatedActualASupportTrain
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S)) :
    EdgeTrainLevels
      {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) //
        e ∈ actualACopyCarriers A
          (RelStructure.Attachment.attach B S D f)} m :=
  (physicalPictureGeneratedTrain
    oldTrain coreTrain
    (sharedOldACarrierInclusion A B S)
    (sharedOldACarrierCoreEmbedding A B S D f)
    hShared).transport (actualAPictureEdgeEquiv A hA B S D f)

/-- Every generated wagon equivalence of two PRESENTED physical
A-support edges is exactly the corresponding old/core generator
closure at that cut. -/
theorem generatedActualASupportTrain_rel_iff
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
    (μ : Fin (m + 1))
    (a b : ActualAPicturePushoutEdge A B S D I) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).rel μ
        (actualAPictureEdgeEquiv A hA B S D f a)
        (actualAPictureEdgeEquiv A hA B S D f b) ↔
    TrainEdgeGenerated
      (physicalPictureCutStep oldTrain coreTrain μ
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f))
      a b := by
  exact EdgeTrainLevels.transport_rel_iff
    (physicalPictureGeneratedTrain
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hShared)
    (actualAPictureEdgeEquiv A hA B S D f) μ a b

/-- Every genuine labelled wagon in the ACTUAL attached
A-support hypergraph has exactly the vertex carrier of
its canonical presented old/core generated wagon. -/
theorem generatedActualASupportTrain_wagonCarrier_eq
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
    (μ : Fin (m + 1))
    (a : ActualAPicturePushoutEdge A B S D I) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).wagonCarrier
        (fun e : {e : Set (RelStructure.Attachment.Vertex S
            (W := Core) (I := I)) //
          e ∈ actualACopyCarriers A
            (RelStructure.Attachment.attach B S D f)} => e.1)
        μ (actualAPictureEdgeEquiv A hA B S D f a) =
      (physicalPictureGeneratedTrain
        oldTrain coreTrain
        (sharedOldACarrierInclusion A B S)
        (sharedOldACarrierCoreEmbedding A B S D f)
        hShared).wagonCarrier
          (fun x : ActualAPicturePushoutEdge A B S D I =>
            (actualAPictureEdgeEquiv A hA B S D f x).1)
          μ a := by
  exact EdgeTrainLevels.transport_wagonCarrier_eq
    (physicalPictureGeneratedTrain
      oldTrain coreTrain
      (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f)
      hShared)
    (actualAPictureEdgeEquiv A hA B S D f)
    (fun x : ActualAPicturePushoutEdge A B S D I =>
      (actualAPictureEdgeEquiv A hA B S D f x).1)
    (fun e : {e : Set (RelStructure.Attachment.Vertex S
        (W := Core) (I := I)) //
      e ∈ actualACopyCarriers A
        (RelStructure.Attachment.attach B S D f)} => e.1)
    (by intro x; rfl) μ a

end StructuralRamsey.Girth
