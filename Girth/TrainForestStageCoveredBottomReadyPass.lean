import Girth.TrainForestStageBottomReadyPass
import Girth.TrainActualSelectedBaseCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# Correct finite-pass readiness: bottom girth PLUS selected base lifts

The only additional SYSTEM-GIRTH invariant is bottom q, but the
checked source-supremeness transfer asks for strongness of every
prescribed base B-copy. ActiveAttachmentBounds provides that
only for SELECTED copies. To derive the old theorem's stronger input,
each base B-copy must have a selected lift.

This base-coverage assertion is a transport invariant, not a new
Ramsey premise: it holds in the initial disjoint picture and every
selected TransitionEmbedding preserves it. A PictureStep itself
provides such a transition by choosing one constant colouring.

The finite readiness state therefore carries (BottomReady AND
CoversBase). Given a bottom-preserving selected PictureStep at every
profile, the existing finite pass gives a final OrderStage and a
selected strong train Ramsey arrow with no all-base strongness
oracle. No chosen lower-rank witness is assumed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (RelStructure.Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- The actual finite-pass readiness condition. The first field
(bottom girth) is the new system bound. The second (selected base
coverage) is automatically transported by a selected PictureStep. -/
def ForestTailStage.CoveredBottomReady
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed) :
    Prop :=
  S.BottomReady ∧ S.CoversBase

/-- The checked finite Ramsey pass, supplied with genuinely selected
bottom-preserving local picture steps, returns a final ORDER stage
and selected Ramsey arrow. The selected-lift coverage required by
the physical source transfer is carried automatically along every
picture transition. Neither the stronger all-family strongness
premise nor a separate per-step coverage assumption is needed. -/
theorem ForestTailStage.ramseyOrderPass_of_covered_bottom_steps
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.CoveredBottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.CoveredBottomReady →
        ∃ R : ForestTailStage A B D family (q :: tail) targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      DesignatedArrow R.toForestTailStage κ := by
  let Ready : List (UA ↪ P) →
      ForestTailStage A B D family (q :: tail) targetTrain allowed → Prop :=
    fun _ T => T.CoveredBottomReady
  have hStep :
      ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
        (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
        Ready (α :: remaining) T →
        ∃ R : ForestTailStage A B D family (q :: tail) targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ := by
    intro α remaining T hT
    obtain ⟨R, hBottomR, hPicture⟩ := step α remaining T hT
    have hCoverR : R.CoversBase :=
      hPicture.coversBase hT.2
    exact ⟨R, ⟨hBottomR, hCoverR⟩, hPicture⟩
  obtain ⟨T, hTReady, hArrow⟩ :=
    S.ramseyPass profiles κ Ready hInitial hProfiles hBase
      hInitial.2 hStep
  let R := T.withBottomSystemGirth hTReady.1
  exact ⟨R, hArrow⟩

/-- The returned Ramsey arrow is STRONG and preserves/refelects the
original train relations at every actual horizontal coordinate.
There is no additional selection step or target-label quotient. -/
theorem ForestTailStage.ramseyOrderPass_strong_train_of_covered
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.CoveredBottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.CoveredBottomReady →
        ∃ R : ForestTailStage A B D family (q :: tail) targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      ∀ χ : RelStructure.Embedding A R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family, b ∈ R.selected ∧
          AStrong A R.system.toRelStructure (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : RelStructure.Embedding A B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : RelStructure.Embedding A B,
            χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  obtain ⟨R, hArrow⟩ :=
    S.ramseyOrderPass_of_covered_bottom_steps
      profiles κ hInitial hProfiles hBase step
  refine ⟨R, ?_⟩
  intro χ
  exact hArrow.strongTrain χ

end StructuralRamsey.Girth.TrainRecursiveWitness
