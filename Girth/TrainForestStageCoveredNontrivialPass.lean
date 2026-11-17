import Girth.TrainForestStageCoveredBottomReadyPass
import Girth.TrainRecursiveNontrivialFibre
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Same-vector F_t -> R_t finite pass: only NONTRIVIAL physical fibres

The checked finite profile dispatcher already uses the identity
picture step whenever a projected A-fibre has at most one distinct
physical A-copy. For ordered A, it only requests an actual local
picture operator on fibres containing two different physical copies.

The concrete readiness condition for the forest-to-order pass is
BottomReady AND CoversBase. It is independent of the list of
unprocessed profiles: the identity step retains it automatically.
For a genuine order-attachment, bottom girth follows from the
output OrderStage, and selected base coverage follows from the
transition map inherent in PictureStep.

Thus the complete finite pass reduces to ONE actual nontrivial
local operator. This operator is expected to be implemented by
F_t at the SAME cutoff vector using the raw local-witness adapter;
its existence is NOT assumed to follow from a weaker theorem.

The result is an actual OrderStage and an original selected strong
B-target train Ramsey arrow, preserving all physical A-edges and
train equivalence relations. No new lower-rank recursive witness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Given bottom-ready selected coverage and a REAL local selected
order picture step on every nontrivial physical profile, the checked
profile dispatcher constructs the next bottom-ready selected step.
The subsingleton case uses identity, not a fictitious one-edge F_t
attachment or a separately supplied skip-readiness hypothesis. -/
theorem ForestTailStage.covered_profileStep_of_nontrivial_order
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (α : UA ↪ P) (remaining : List (UA ↪ P))
    (κ : Type w) [Nonempty κ]
    (hReady : S.CoveredBottomReady)
    (actualStep : ∀ (e : Embedding A D),
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
        PictureStep S R.toForestTailStage e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family (q :: tail) targetTrain allowed,
      T.CoveredBottomReady ∧ PictureStep S T α κ := by
  let Ready : List (UA ↪ P) →
      ForestTailStage A B D family (q :: tail) targetTrain allowed → Prop :=
    fun _ T => T.CoveredBottomReady
  apply ForestTailStage.profileStep_of_nontrivialStep
    A₀ S α remaining κ Ready hReady
  · intro _hSmall
    exact hReady
  · intro e hPair _hReady
    obtain ⟨R, hPicture⟩ := actualStep e hPair
    have hBaseR : R.toForestTailStage.CoversBase :=
      hPicture.coversBase hReady.2
    have hBottomR : R.toForestTailStage.BottomReady := by
      simpa using R.allCutGirth
        (⟨0, by simp⟩ : Fin (q :: tail).length)
    exact ⟨R.toForestTailStage, ⟨hBottomR, hBaseR⟩, hPicture⟩

/-- The complete selected strong-train finite Ramsey pass requires
only ONE nontrivial-fibre local-order operator. The original B-copy
strongness, all horizontal train reflection laws, actual selected
copies and the exact q :: tail system cutoffs are retained. There
is no independent skip-readiness law or extra initial strongness. -/
theorem ForestTailStage.ramseyOrderPass_of_nontrivial_order_steps
    (S : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.CoveredBottomReady)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (actualStep : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: tail) targetTrain allowed),
      T.CoveredBottomReady →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A T.system
        e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
        PictureStep T R.toForestTailStage e.toFunctionEmbedding κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      ∀ χ : Embedding A R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family,
          b ∈ R.selected ∧
          AStrong A R.system.toRelStructure (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : Embedding A B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : Embedding A B,
            χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  apply S.ramseyOrderPass_strong_train_of_covered
    profiles κ hInitial hProfiles hBase
  intro α remaining T hReady
  exact T.covered_profileStep_of_nontrivial_order A₀
    α remaining κ hReady (fun e hPair => actualStep e remaining T hReady hPair)

end StructuralRamsey.Girth.TrainRecursiveWitness
