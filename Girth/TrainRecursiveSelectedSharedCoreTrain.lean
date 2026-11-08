import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# True selected lower-stage restriction on EVERY shared physical A-edge

The generic shared-core train theorem previously required an independently
supplied fine hRestriction equivalence. When the lower recursive witness
is an ACTUAL selected ForestTailStage over precisely the induced active
source, this equivalence follows from its checked targetRestriction
field for every selected designated copy.

The source train is indexed by all complete shared physical A-carriers.
The genuine selected lower copy is transported to the core through its
real vertex embedding. We keep every label and every train cut, including
the equality and universal-top cuts; no hFaithful assumption is added.
The theorem is conditional on existence of the actual lower stage,
not a recursive witness-existence result.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA X Y : Type v}

/-- The selected lower stage automatically reflects and preserves the
genuine shared-edge source train when its target train is the literal
physical restriction along inducedACarrierToShared. No independently
assumed selected physical train map or relation-reflection premise. -/
theorem ForestTailStage.selectedSharedCore_train_iff_of_actualLower
    (A : RelStructure L UA)
    (B : RelStructure L X) (active : Set X)
    (D : RelStructure L Y)
    {family : Set (Embedding (B.induce active) D)}
    {t : List ℕ}
    (source : EdgeTrainLevels (SharedOldACarrierEdge A B active) t.length)
    (allowed : Fin (t.length + 1) → Set Y)
    (lower : ForestTailStage A (B.induce active) D family t
      (source.restrict (inducedACarrierToShared A B active)) allowed)
    (μ : Fin (t.length + 1))
    (i : {b : DesignatedCopy (B.induce active) D lower.system family //
      b ∈ lower.selected})
    (p q : SharedOldACarrierEdge A B active) :
    source.rel μ p q ↔
      lower.train.rel μ
        (sharedOldACarrierCoreEmbedding A B active
          lower.system.toRelStructure
          (fun j : {b : DesignatedCopy (B.induce active) D
            lower.system family // b ∈ lower.selected} =>
            j.1.embedding) i p)
        (sharedOldACarrierCoreEmbedding A B active
          lower.system.toRelStructure
          (fun j : {b : DesignatedCopy (B.induce active) D
            lower.system family // b ∈ lower.selected} =>
            j.1.embedding) i q) := by
  exact sharedCore_train_iff_of_prescribedRestriction
    A B active lower.system.toRelStructure
    (fun j : {b : DesignatedCopy (B.induce active) D
      lower.system family // b ∈ lower.selected} =>
      j.1.embedding)
    source lower.train
    (fun ν j a b => lower.targetRestriction j.1 j.2 ν a b)
    μ i p q

end StructuralRamsey.Girth.TrainRecursiveWitness
