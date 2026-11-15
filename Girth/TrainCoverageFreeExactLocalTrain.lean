import Girth.TrainRecursiveFineWitnessTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact same-vector shared-train compatibility from local F_t embeddings

The circulation F_t assertion supplies a selected family of actual
train embeddings T -> H. Each preserves AND reflects every wagon
relation, not just the proper positive cuts.

The true active source has two literal physical restrictions:
first from all old A-edges to complete edges carried by the
active vertex set, then from those shared edges to relational
A-edges of the induced active subsystem. The local F_t witness
uses that honest doubly restricted train as its prescribed target.

The already checked
sharedCore_train_iff_of_prescribedRestriction theorem upgrades
these selected train-embedding restrictions to the EXACT
old-to-local shared-core relation hRel required in the physical
bottom forest preservation and the coverage-free attachment.
This holds at EVERY original cut, including equality bottom and
universal top. No new mixed irreducible coverage, staged lower
witness, parent-label quotient or extra "faithfulness" axiom.

The premise below is precisely the train-embedding condition
promised by F_t for the ACTUAL selected family. Its finite
existence remains the abstract forest assertion, not a new
implicit recursive witness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v

/-- F_t's exact selected train-embedding law on every induced
physical A-edge gives the full original shared-edge train
preservation/reflection needed by the next picture step.
This is a direct use of the checked physical restriction theorem. -/
theorem originalSharedTrain_iff_of_selectedFt_embeddings
    {L : RelLanguage.{u}} {UA X Y I : Type v}
    (A : RelStructure L UA)
    (Old : RelStructure L X) (S : Set X)
    (Core : RelStructure L Y)
    (f : I → Embedding (Old.induce S) Core)
    {m : ℕ}
    (oldTrain : EdgeTrainLevels
      (OldACarrierEdge A Old) m)
    (localTrain : EdgeTrainLevels
      (OldACarrierEdge A Core) m)
    (hSelectedTrain : ∀ (μ : Fin (m + 1)) (i : I)
      (a b : Embedding A (Old.induce S)),
      localTrain.rel μ
        (actualEdge ((f i).comp a))
        (actualEdge ((f i).comp b)) ↔
      (((oldTrain.restrict
        (sharedOldACarrierInclusion A Old S)).restrict
        (inducedACarrierToShared A Old S)).rel μ)
          (actualEdge a) (actualEdge b)) :
    ∀ (μ : Fin (m + 1)) (i : I)
      (p q : SharedOldACarrierEdge A Old S),
      oldTrain.rel μ p.1 q.1 ↔
        localTrain.rel μ
          (sharedOldACarrierCoreEmbedding
            A Old S Core f i p)
          (sharedOldACarrierCoreEmbedding
            A Old S Core f i q) := by
  intro μ i p q
  change
    (oldTrain.restrict
      (sharedOldACarrierInclusion A Old S)).rel μ p q ↔
    localTrain.rel μ
      (sharedOldACarrierCoreEmbedding A Old S Core f i p)
      (sharedOldACarrierCoreEmbedding A Old S Core f i q)
  exact sharedCore_train_iff_of_prescribedRestriction
    A Old S Core f
    (oldTrain.restrict
      (sharedOldACarrierInclusion A Old S))
    localTrain hSelectedTrain μ i p q

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
