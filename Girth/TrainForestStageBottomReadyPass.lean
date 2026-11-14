import Girth.TrainForestStageToOrderStage
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The only extra finite-pass readiness field: bottom system girth

ForestTailStage already includes the complete forest property,
selected B-copies, exact physical train, all adjacent parameters,
target train reflection and the positive system-girth coordinates.

To obtain OrderStage at the SAME nonempty vector q :: tail,
the finite Ramsey pass only has to preserve the bottom bound at q.
This is an explicit one-field invariant, not a fictitious
construction of the local F_t witnesses.

The existing finite-pass/selected-arrow theorem then gives a final
OrderStage and a selected strong target train arrow once a real
bottom-preserving PictureStep is supplied for every processed
profile. Neither top system-girth nor another recursive witness
is introduced.
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

/-- The genuine readiness predicate needed by the SAME-vector
forest-to-order finite pass: bottom q, and nothing more.
All other positive-cut and train data are carried by S itself. -/
def ForestTailStage.BottomReady
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed) :
    Prop :=
  (selectedPictureOrderOneData A B D S.system family S.selected
    S.train (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q

/-- Every actual finite succession of bottom-preserving selected
PictureSteps yields a selected-arrow OrderStage at the SAME vector.
The step hypothesis is deliberately a REAL existential for the
next stage; it must be supplied by either the nontrivial F_q witness
or the single-edge local-target picture-step constructor.
No terminal readiness oracle is assumed. -/
theorem ForestTailStage.ramseyOrderPass_of_bottom_preserving_steps
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.BottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ a : DesignatedCopy B D S.system family,
        a ∈ S.selected ∧ a.base = b)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.BottomReady →
        ∃ R : ForestTailStage A B D family (q :: tail) targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ T : OrderStage A B D family (q :: tail) targetTrain allowed,
      DesignatedArrow T.toForestTailStage κ := by
  obtain ⟨R, hFinal, hArrow⟩ :=
    S.ramseyPass profiles κ
      (fun _ T => T.BottomReady)
      hInitial hProfiles hBase hLift step
  let T := R.withBottomSystemGirth hFinal
  exact ⟨T, hArrow⟩

/-- The final selected monochromatic copy in that order stage
retains the original train-relation reflection and is A-strong.
This is a direct use of the checked strongTrain extraction rather
than merely forgetting the selected family to an ordinary arrow. -/
theorem ForestTailStage.ramseyOrderPass_strong_train
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.BottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ a : DesignatedCopy B D S.system family,
        a ∈ S.selected ∧ a.base = b)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.BottomReady →
        ∃ R : ForestTailStage A B D family (q :: tail) targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ T : OrderStage A B D family (q :: tail) targetTrain allowed,
      ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D T.system family, b ∈ T.selected ∧
          AStrong A T.system.toRelStructure (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : RelStructure.Embedding A B,
              T.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : RelStructure.Embedding A B,
            χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  obtain ⟨T, hArrow⟩ :=
    S.ramseyOrderPass_of_bottom_preserving_steps
      profiles κ hInitial hProfiles hBase hLift step
  refine ⟨T, ?_⟩
  intro χ
  exact hArrow.strongTrain χ

end StructuralRamsey.Girth.TrainRecursiveWitness
