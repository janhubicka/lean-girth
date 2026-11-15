import Girth.TrainCoverageFreePhysicalFibre
import Girth.TrainCoverageFreeOrderPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Final coverage-free selected strong-train finite Ramsey pass

The checked Ramsey finite-pass proof and physical-fibre dispatcher
both ignore the recursive mixedCoverage field. Their actual
coverage-free counterparts are now available:

- subsingleton ordered physical A-fibres use the identity stage;
- only nontrivial physical fibres require a selected local F_t step;
- a genuine selected transition preserves every prescribed B-base
  selected lift, with its original base embedding;
- full bottom system girth is retained by the actual next OrderStage;
- all positive full bounds, mixed forests and part parameters are
  already fields of the coverage-free ForestStage.

Consequently an actual selected strong target-train Ramsey arrow
at the SAME q::tail vector follows from one local F_t operator on
each nontrivial fibre, with no coverage of ambient irreducibles
assumed for arbitrary F_t witnesses.

This is a conditional finite COMBINATORIAL theorem: the local
operator is explicitly an actual selected PictureStep into an
OrderStage. Its construction from the F_t partite witness is
handled by TrainCoverageFreeNontrivialFtStep, still uncompiled.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain :
  EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Full SAME-VECTOR selected strong train Ramsey pass from actual
F_t selected local OrderStage steps on nontrivial physical fibres.
Every skipped fibre is an identity step; every attached fibre
transports the selected base lifts. The conclusion retains all
original target train relations and their reflections. -/
theorem ForestStage.ramseyStrongTrain_of_nontrivialFtSteps
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.Ready)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBaseArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (localFt : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family (q :: tail) targetTrain allowed),
      T.Ready →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
        A T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      ∃ O : OrderStage A B D family (q :: tail) targetTrain allowed,
        PictureStep T O.toForestStage e.toFunctionEmbedding κ) :
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
  apply S.ramseyStrongTrain_of_ready_steps
    profiles κ hInitial hProfiles hBaseArrow
  intro α remaining T hReady
  let Ready : List (UA ↪ P) →
      ForestStage A B D family (q :: tail) targetTrain allowed → Prop :=
    fun _ Q => Q.Ready
  have hSkip :
      (Set.range (fun a :
        StructuralRamsey.Partite.ProjectedEmbedding A T.system α =>
          copyCarrier a.val)).Subsingleton → Ready remaining T :=
    fun _ => hReady
  have hActual :
      ∀ e : Embedding A D,
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
        A T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      Ready (e.toFunctionEmbedding :: remaining) T →
      ∃ Q : ForestStage A B D family (q :: tail) targetTrain allowed,
        Ready remaining Q ∧
        PictureStep T Q e.toFunctionEmbedding κ := by
    intro e hTwo _hCurrent
    obtain ⟨O, hPicture⟩ := localFt e remaining T hReady hTwo
    have hNextBottom : O.toForestStage.BottomReady := by
      simpa using O.allCutGirth
        (⟨0, by simp⟩ : Fin (q :: tail).length)
    have hNextCover : O.toForestStage.CoversBase :=
      hPicture.coversBase hReady.2
    exact ⟨O.toForestStage, ⟨hNextBottom, hNextCover⟩, hPicture⟩
  obtain ⟨TNext, hReadyNext, hPicture⟩ :=
    T.profileStep_of_nontrivialStep A₀
      α remaining κ Ready hReady hSkip hActual
  exact ⟨TNext, hReadyNext.1, hPicture⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
