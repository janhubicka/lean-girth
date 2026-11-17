import Girth.TrainCoverageFreeOrderPass

set_option autoImplicit false
set_option Elab.async false

/-!
# The existing selected finite pass embeds into the coverage-free pass

The weaker ForestStage does not change any actual train, selected
B-copy or physical A-edge. Every previously checked strong stage,
selected TransitionEmbedding, PictureStep and selected DesignatedArrow
has a literal image in the new coverage-free presentation.

This makes the construction backward-compatible with the earlier
recursive implementation, while making explicit that the converse
requires a genuine mixedCoverage proof. No new Ramsey or geometric
assumptions are introduced.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Forgetting the extra mixedCoverage proof takes a checked selected
train transition to a literal coverage-free selected transition. -/
def TransitionEmbedding.ofStrong
    {S T : TrainRecursiveWitness.ForestTailStage
      A B D family t targetTrain allowed}
    (f : TrainRecursiveWitness.TransitionEmbedding S T) :
    TransitionEmbedding (ForestStage.ofStrong S)
      (ForestStage.ofStrong T) where
  toPartite := f.toPartite
  map_selected := f.map_selected
  train_iff := f.train_iff

/-- The checked selected picture-step is still valid with exactly
the same physical images and colouring once irreducible coverage is
forgotten. The selected embedding is unchanged. -/
theorem PictureStep.ofStrong
    {S T : TrainRecursiveWitness.ForestTailStage
      A B D family t targetTrain allowed}
    {α : UA ↪ P} {κ : Type w}
    (h : TrainRecursiveWitness.PictureStep S T α κ) :
    PictureStep (ForestStage.ofStrong S)
      (ForestStage.ofStrong T) α κ := by
  intro χ
  obtain ⟨f, hf⟩ := h χ
  exact ⟨TransitionEmbedding.ofStrong f, hf⟩

/-- A checked original selected Ramsey-arrow certificate survives
forgetting mixed irreducible coverage. This does not take any
quotient of selected labels or replace its target. -/
theorem DesignatedArrow.ofStrong
    {S : TrainRecursiveWitness.ForestTailStage
      A B D family t targetTrain allowed}
    {κ : Type w}
    (h : TrainRecursiveWitness.DesignatedArrow S κ) :
    DesignatedArrow (ForestStage.ofStrong S) κ :=
  h

/-- The complete previously checked order stage is still a
coverage-free order stage, with the same system, train and cut
bounds; it does not require a second girth proof. -/
theorem OrderStage.ofStrong_cutGirth
    (S : TrainRecursiveWitness.OrderStage
      A B D family t targetTrain allowed)
    (j : Fin t.length) :
    (selectedPictureOrderOneData A B D
      (OrderStage.ofStrong S).system family
      (OrderStage.ofStrong S).selected
      (OrderStage.ofStrong S).train j.castSucc)
        .FullSystemGirthGT (t.get j) :=
  (OrderStage.ofStrong S).allCutGirth j

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
