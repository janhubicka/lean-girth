import Girth.TrainRecursiveSelectedWitnessConsequences
import Girth.TrainRecursiveTrueActiveCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# Core fine-witness inputs from the actual active fibre and the lower stage

The previous modules established two different parts of the q > 2
recursion: the old stage gives irreducible A-coverage of its true active
subsystem at girth greater than three; a genuine lower selected stage
gives partiteness, local A-coverage, selected physical injectivity and
the mixed forest bound after coarsening.

This module composes those theorems with the literal active relational
target. In particular the local target-coverage premise is derived from
the old stage, rather than being passed as an extra hypothesis. The
selected gluing family still consists of the genuine selected-copy
subtype, with no quotient of labels or deletion of ambient A-edges.

The construction of the lower stage, fine train restrictions, positive
system-girth, parameters and attached-output SupremeCycleBound remain
distinct obligations. No full recursive witness existence is asserted.
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

local notation "Source" =>
  old.system.toRelStructure.induce
    (activeCarrier A old.system e.toFunctionEmbedding)
local notation "Target" =>
  actualActiveSubsystemPartite A old.system e.toFunctionEmbedding

variable (large : StructuralRamsey.Partite.System L UA Q)
variable {lowerFamily : Set (Embedding Source large.toRelStructure)}
variable {lowerCutoffs : List ℕ}
variable {lowerTrain : EdgeTrainLevels (OldACarrierEdge A Source) lowerCutoffs.length}
variable {lowerAllowed : Fin (lowerCutoffs.length + 1) → Set Q}
variable (lower : ForestTailStage A Source large.toRelStructure
  lowerFamily lowerCutoffs lowerTrain lowerAllowed)
variable (hFamilyParts : ∀ b, b ∈ lowerFamily →
  ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
    large.part (b x) = activeSourcePart A old.system e.toFunctionEmbedding x)

local notation "Gluing" =>
  selectedPartiteGluingFamily_of_largeBase Target large lower.system
    lower.isPartite lowerFamily hFamilyParts lower.selected
local notation "Selected" =>
  {q : DesignatedCopy Source large.toRelStructure lower.system lowerFamily //
    q ∈ lower.selected}

/-- The true active target's A-extension is derived *before* applying
the coarsened lower-stage result. Four physical fine-witness inputs
then follow, without assuming an independent A-coverage witness. -/
theorem ForestTailStage.coarsenedFineInputs_of_trueActive
    (hA : A.Irreducible)
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base))
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A old.system e.toFunctionEmbedding).Nonempty)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding)
    (hHigh : 3 ≤ t.headD 0)
    (hLarge : large.IsPartiteOver A)
    (q : ℕ) (hq : q ≤ lowerCutoffs.headD 0) :
    (lower.system.coarsenVia large lower.isPartite).IsPartiteOver A ∧
    IrreduciblesExtendTo A
      (lower.system.coarsenVia large lower.isPartite).toRelStructure ∧
    Function.Injective (fun i : Selected =>
      bSupportPiece A (Gluing i).toEmbedding) ∧
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i : Selected =>
        (Gluing i).toEmbedding)) q := by
  have hTarget : IrreduciblesExtendTo A (Target).toRelStructure :=
    old.trueActive_irreduciblesExtendTo hA hBaseLinear
      hBaseStrong e hRigid hActive projected hHigh
  exact lower.coarsenedSelected_fineWitnessInputs
    A Target large hLarge hTarget hFamilyParts q hq

end StructuralRamsey.Girth.TrainRecursiveWitness
