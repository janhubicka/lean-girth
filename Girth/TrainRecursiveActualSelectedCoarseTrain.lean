import Girth.TrainRecursiveSelectedSharedCoreTrain
import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact coarse shared-train reflection from a genuine refined lower stage

The lower selected ForestTailStage is over the literal induced true active
source, with the full prescribed fine target train obtained by restricting
the actual first-wagon refinement and transporting only its height index.

At every OLD cut, including zero and the universal top, the forgotten
lower physical train preserves AND reflects the original full shared
A-edge train relation on every selected lower copy. This is not a free
hRel hypothesis for Path A's attached-output theorem. The proof uses
the real lower stage's targetRestriction and the previously audited
coarseSharedTrain_iff_of_finePrescribedRestriction, including the
bottom/equality special case.

No physical edge, designated copy index, or wagon label is deleted,
identified, or replaced. The lower selected stage is a genuine input;
this does not construct it or assert a nontrivial PictureStep.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y : Type v}

/-- An actual lower selected forest stage whose target train is exactly
the refined true active train automatically supplies the old-to-coarse
shared-edge reflection required by the original-source picture argument.
The finite train-height equality changes only Fin indices. -/
theorem ForestTailStage.coarseSharedTrain_iff_of_realRefinedLower
    (A : RelStructure L UA)
    (B : RelStructure L X) (active : Set X)
    (D : RelStructure L Y)
    {family : Set (Embedding (B.induce active) D)}
    {m : ℕ} (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (hm : 0 < m)
    {edge : SharedOldACarrierEdge A B active → Set X}
    {part : X → P} {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement
      (oldTrain.restrict (sharedOldACarrierInclusion A B active))
      hm edge part firstAllowed g)
    {cuts : List ℕ} (hLen : cuts.length = m + R.extraCuts)
    (allowed : Fin (cuts.length + 1) → Set Y)
    (lower : ForestTailStage A (B.induce active) D family cuts
      ((R.train.restrict (inducedACarrierToShared A B active)).castHeight hLen.symm)
      allowed)
    (μ : Fin (m + 1))
    (i : {b : DesignatedCopy (B.induce active) D lower.system family //
      b ∈ lower.selected})
    (p q : SharedOldACarrierEdge A B active) :
    oldTrain.rel μ p.1 q.1 ↔
      ((lower.train.castHeight hLen).forgetFirstCuts hm).rel μ
        (sharedOldACarrierCoreEmbedding A B active
          lower.system.toRelStructure
          (fun j : {b : DesignatedCopy (B.induce active) D
            lower.system family // b ∈ lower.selected} => j.1.embedding) i p)
        (sharedOldACarrierCoreEmbedding A B active
          lower.system.toRelStructure
          (fun j : {b : DesignatedCopy (B.induce active) D
            lower.system family // b ∈ lower.selected} => j.1.embedding) i q) := by
  cases hLen
  exact coarseSharedTrain_iff_of_finePrescribedRestriction
    A B active lower.system.toRelStructure
    (fun j : {b : DesignatedCopy (B.induce active) D
      lower.system family // b ∈ lower.selected} => j.1.embedding)
    oldTrain hm R lower.train
    (fun ν j a b => lower.targetRestriction j.1 j.2 ν a b)
    μ i p q

end StructuralRamsey.Girth.TrainRecursiveWitness
