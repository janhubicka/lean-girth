import Girth.TrainGeneratedActualAllLevelRestriction
import Girth.TrainWagonClassRestriction

/-!
# The core wagon class is an injectively labelled output wagon

The exact core restriction theorem is a relation *equivalence* on
genuine physical A-support edges, not merely a preservation map. It
therefore descends to an injective map of wagon quotient classes, at
every train cut. This makes the intended core-to-output wagon map
available to the cut-indexed witness reduct.

The map alone does not prove that a particular boundary output wagon
is in its image; the owner-cut incidence theorem must still retain
and identify the connector at each cut. No system-Girth preservation
or full cycle-reduction conclusion is asserted here.
-/

namespace StructuralRamsey.Girth

universe u v

/-- An edge map reflecting *and* preserving a wagon relation descends
to an injective map of quotient wagon labels. Neither equality of
wagon carriers nor an invented choice of representatives is used. -/
noncomputable def EdgeTrainLevels.wagonEmbeddingOfRelationIff
    {E F : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (U : EdgeTrainLevels F m)
    (μ : Fin (m + 1)) (f : E → F)
    (hRel : ∀ a b : E, U.rel μ (f a) (f b) ↔ T.rel μ a b) :
    Quotient (T.wagonSetoid μ) ↪ Quotient (U.wagonSetoid μ) := by
  let map : Quotient (T.wagonSetoid μ) →
      Quotient (U.wagonSetoid μ) :=
    fun c => Quotient.liftOn c
      (fun a : E => Quotient.mk (U.wagonSetoid μ) (f a))
      (by
        intro a b hab
        exact Quotient.sound ((hRel a b).2 hab))
  refine ⟨map, ?_⟩
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      change Quotient.mk (U.wagonSetoid μ) (f a) =
        Quotient.mk (U.wagonSetoid μ) (f b) at hxy
      exact Quotient.sound ((hRel a b).1 (Quotient.exact hxy))

@[simp] theorem EdgeTrainLevels.wagonEmbeddingOfRelationIff_mk
    {E F : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (U : EdgeTrainLevels F m)
    (μ : Fin (m + 1)) (f : E → F)
    (hRel : ∀ a b : E, U.rel μ (f a) (f b) ↔ T.rel μ a b)
    (a : E) :
    T.wagonEmbeddingOfRelationIff U μ f hRel
      (Quotient.mk (T.wagonSetoid μ) a) =
      Quotient.mk (U.wagonSetoid μ) (f a) := rfl

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}

/-- The *actual* core-to-output wagon map for the generated relational
A-support picture. Its injectivity uses the proved equivalence of
core and generated wagon relations, with genuine shared-train
preservation as the explicit hypothesis. -/
noncomputable def generatedActualASupportTrain_coreWagonEmbedding
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
    (μ : Fin (m + 1)) :
    Quotient (coreTrain.wagonSetoid μ) ↪
      Quotient ((generatedActualASupportTrain A hA B S D f
        oldTrain coreTrain hShared).wagonSetoid μ) :=
  coreTrain.wagonEmbeddingOfRelationIff
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared) μ
    (fun a : OldACarrierEdge A D =>
      actualAPictureEdgeEquiv A hA B S D f
        (physicalCoreEdge (sharedOldACarrierInclusion A B S) I a))
    (fun a b =>
      generatedActualASupportTrain_restrict_core
        A hA B S D f oldTrain coreTrain hPreserve hShared μ a b)

/-- For a core support edge, the embedded class is *definitionally*
the generated physical wagon containing that genuine core edge. -/
theorem generatedActualASupportTrain_coreWagonEmbedding_mk
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
    (μ : Fin (m + 1)) (a : OldACarrierEdge A D) :
    generatedActualASupportTrain_coreWagonEmbedding
      A hA B S D f oldTrain coreTrain hPreserve hShared μ
      (Quotient.mk (coreTrain.wagonSetoid μ) a) =
    Quotient.mk
      ((generatedActualASupportTrain A hA B S D f
        oldTrain coreTrain hShared).wagonSetoid μ)
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalCoreEdge (sharedOldACarrierInclusion A B S) I a)) := rfl

end StructuralRamsey.Girth
