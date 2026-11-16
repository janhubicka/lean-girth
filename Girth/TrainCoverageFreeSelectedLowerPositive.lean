import Girth.TrainCoverageFreeSelectedLowerBundle
import Girth.TrainCoverageFreeExactLocalTrain
import Girth.TrainRecursiveSelectedGluingIncidence
import Girth.ActualActivePartitePresentation
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Coverage-free lower F_t: exact original shared train and positive system bounds

The coarsened selected lower witness is an ARBITRARY coverage-free
ForestStage. In particular, no recursive mixedCoverage field exists.

Its original selected train-embedding restriction transfers to the
true active source's old shared physical wagon relations at every cut.
Its stored positive FullSystemGirthGT yields the genuine positive
active-gluing FULL-system certificate, via the checked equivalence
of the original selected picture with the literal gluing family.

Both statements keep the ORIGINAL selected subtype as their index.
No quotient of labels and no external output-girth hypothesis occur.

Source-only/uncompiled: this is not a Lean kernel certificate.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X V : Type v}

variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (Large : StructuralRamsey.Partite.System L UA V)

local notation "Active" =>
  activeCarrier A Old α
local notation "Target" =>
  Old.toRelStructure.induce Active
local notation "OldTrain" =>
  (fun (train : EdgeTrainLevels
    (OldACarrierEdge A Old.toRelStructure) 0) => train)

section ExactLower

variable {family : Set (Embedding Target Large.toRelStructure)}
variable {t : List ℕ}
variable (oldTrain : EdgeTrainLevels
  (OldACarrierEdge A Old.toRelStructure) t.length)
variable (fineAllowed : Fin (t.length + 1) → Set UA)
variable (lower : ForestStage A Target Large.toRelStructure
  family t
  (((oldTrain.restrict
    (sharedOldACarrierInclusion A Old.toRelStructure Active)).restrict
    (inducedACarrierToShared A Old.toRelStructure Active)))
  (fun ν => Large.part ⁻¹' fineAllowed ν))
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : Active,
    Large.part (b x) = activeSourcePart A Old α x)

local notation "Coarse" =>
  lower.system.coarsenVia Large lower.isPartite
local notation "Selected" =>
  {b : DesignatedCopy Target Large.toRelStructure lower.system family //
    b ∈ lower.selected}
local notation "F" =>
  (fun i : Selected =>
    (selectedPartiteGluingFamily_of_largeBase
      (actualActiveSubsystemPartite A Old α)
      Large lower.system lower.isPartite family hFamilyParts
      lower.selected i).toEmbedding)

/-- Every selected lower F_t train embedding gives EXACT shared
old-to-local physical train reflection at all cuts, including bottom
equality and universal top. The source uses two true restrictions. -/
theorem ForestStage.sameVector_selected_oldSharedTrain_iff
    (μ : Fin (t.length + 1)) (i : Selected)
    (p q : SharedOldACarrierEdge A Old.toRelStructure Active) :
    oldTrain.rel μ p.1 q.1 ↔
      lower.train.rel μ
        (sharedOldACarrierCoreEmbedding
          A Old.toRelStructure Active Coarse.toRelStructure F i p)
        (sharedOldACarrierCoreEmbedding
          A Old.toRelStructure Active Coarse.toRelStructure F i q) := by
  have hSelectedTrain :
      ∀ (ν : Fin (t.length + 1)) (j : Selected)
        (a b : Embedding A Target),
        lower.train.rel ν
          (actualEdge ((F j).comp a))
          (actualEdge ((F j).comp b)) ↔
        (((oldTrain.restrict
          (sharedOldACarrierInclusion A Old.toRelStructure Active)).restrict
          (inducedACarrierToShared A Old.toRelStructure Active)).rel ν)
            (actualEdge a) (actualEdge b) := by
    intro ν j a b
    change lower.train.rel ν
      (actualEdge (j.1.embedding.comp a))
      (actualEdge (j.1.embedding.comp b)) ↔
        (((oldTrain.restrict
          (sharedOldACarrierInclusion A Old.toRelStructure Active)).restrict
          (inducedACarrierToShared A Old.toRelStructure Active)).rel ν)
            (actualEdge a) (actualEdge b)
    exact lower.targetRestriction j.1 j.2 ν a b
  exact originalSharedTrain_iff_of_selectedFt_embeddings
    A Old.toRelStructure Active Coarse.toRelStructure F
    oldTrain lower.train hSelectedTrain μ i p q

/-- A positive FULL-system certificate follows from the exact
selected-label gluing-system equivalence and lower.tailGirth.
This does not follow merely from ordinary or labelled wagon girth. -/
theorem ForestStage.sameVector_selected_fullSystem_at_positive
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α
      Coarse.toRelStructure F lower.train j.castSucc).FullSystemGirthGT
      (t.get j) := by
  change (activeGluingWitnessOrderOneData A Old α
    lower.system.toRelStructure
    (fun i : Selected => i.1.embedding)
    lower.train j.castSucc).FullSystemGirthGT (t.get j)
  exact (activeGluingWitness_fullSystemGirth_iff_selectedPicture
    A Target Large.toRelStructure Old lower.system
    family lower.selected α
    (fun i : Selected => i.1.embedding)
    lower.train j.castSucc (Equiv.refl _)
    (fun i => rfl) (t.get j)).mpr (lower.tailGirth j hj)

end ExactLower

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
