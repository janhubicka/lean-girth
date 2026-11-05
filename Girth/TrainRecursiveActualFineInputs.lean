import Girth.TrainRecursiveSelectedWitnessConsequences
import Girth.TrainRecursiveTrueActiveCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# Irreducible A-coverage through the actual active lower recursive stage

The original bundle of four local fine-witness inputs is already
proved in TrainRecursiveSelectedWitnessConsequences: local
partiteness, physical injectivity, mixed forest and ordinary
irreducible A-coverage follow from a lower stage PROVIDED its
target has A-coverage.

The genuinely new point is to discharge that last proviso for the
TRUE active subsystem of the old picture, using the verified
high-girth active A-generation theorem. The lower stage's
selected mixed B-or-A coverage then yields ordinary A-coverage
of its FULL relational reduct, unchanged by part coarsening.

Separating this proof from the selected gluing function avoids
re-proving the three other conditions and avoids introducing
implicit new selected-copy labels, false girth of a power, or a
spurious additional geometric assumption.

This is a conditional proof: the actual lower stage and selected
line family still have to be produced; no output SupremeCycleBound
is implied.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Q : Type v}

variable (A : RelStructure L UA)
variable {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (old : ForestTailStage A B D family t targetTrain allowed)
variable (e : Embedding A D)

variable (large : StructuralRamsey.Partite.System L UA Q)
variable {lowerFamily : Set (Embedding (old.system.toRelStructure.induce (activeCarrier A old.system e.toFunctionEmbedding)) large.toRelStructure)}
variable {lowerCutoffs : List ℕ}
variable {lowerTrain : EdgeTrainLevels (OldACarrierEdge A (old.system.toRelStructure.induce (activeCarrier A old.system e.toFunctionEmbedding))) lowerCutoffs.length}
variable {lowerAllowed : Fin (lowerCutoffs.length + 1) → Set Q}
variable (lower : ForestTailStage A (old.system.toRelStructure.induce (activeCarrier A old.system e.toFunctionEmbedding)) large.toRelStructure
  lowerFamily lowerCutoffs lowerTrain lowerAllowed)

/-- The true active target's irreducible A-extension, derived from
old-stage geometry at cutoff at least three, propagates through
the actual lower selected stage. The large base may have many
vertices per A-part and no physical copy or ambient edge is pruned. -/
theorem ForestTailStage.coarsenedAExtension_of_trueActive
    (hA : A.Irreducible)
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base))
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A old.system e.toFunctionEmbedding).Nonempty)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding)
    (hHigh : 3 ≤ t.headD 0) :
    IrreduciblesExtendTo A
      (lower.system.coarsenVia large lower.isPartite).toRelStructure := by
  have hTarget : IrreduciblesExtendTo A (old.system.toRelStructure.induce (activeCarrier A old.system e.toFunctionEmbedding)) :=
    old.trueActive_irreduciblesExtendTo hA hBaseLinear
      hBaseStrong e hRigid hActive projected hHigh
  change IrreduciblesExtendTo A lower.system.toRelStructure
  exact lower.irreduciblesExtendTo_of_target hTarget

end StructuralRamsey.Girth.TrainRecursiveWitness
