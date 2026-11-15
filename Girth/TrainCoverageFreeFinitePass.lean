import Girth.TrainCoverageFreeForestStage
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact finite selected Ramsey pass WITHOUT irreducible coverage

The checked finitePass / allProjections / designatedArrow proof is
purely about selected train transitions, homogeneous projections
and the prescribed base family. None of those proof steps uses the
recursive ForestTailStage.mixedCoverage property.

This module reuses the mathematical argument with only the
coverage-free ForestStage, retaining all the strong selected
B-labels, complete physical A-edges, train relation reflection,
forest invariant, tail girth and part parameters.

The final selected Ramsey arrow still chooses the SAME original
B-labelled target and admits the same strong train reflection.
This is the finite COMBINATORIAL core of the standalone F_t -> R_t
conversion. The remaining work is to implement the actual local
free-attachment operator on ForestStage without requesting the
unpromised mixedCoverage field.

No local F_t witness, output system-girth, inductive construction
or other Ramsey assertion is postulated by this module.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

section Pass

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (RelStructure.Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- A backwards-selection map preserves the selected labels and the entire
train on physical edges.  The selected-copy strongness is carried by the
stage, so it remains available for the final selected Ramsey copy. -/
structure TransitionEmbedding
    (S T : ForestStage A B D family t targetTrain allowed) where
  toPartite : StructuralRamsey.Partite.Embedding S.system T.system
  map_selected : ∀ q : DesignatedCopy B D S.system family,
    q ∈ S.selected → mapDesignated toPartite q ∈ T.selected
  train_iff : ∀ μ : Fin (t.length + 1),
    ∀ a₁ a₂ : RelStructure.Embedding A S.system.toRelStructure,
      T.train.rel μ (actualEdge (toPartite.toEmbedding.comp a₁))
        (actualEdge (toPartite.toEmbedding.comp a₂)) ↔
      S.train.rel μ (actualEdge a₁) (actualEdge a₂)

/-- Identity selection leaves the selected family and all train levels fixed. -/
def TransitionEmbedding.id
    (S : ForestStage A B D family t targetTrain allowed) :
    TransitionEmbedding S S where
  toPartite := StructuralRamsey.Partite.Embedding.id S.system
  map_selected := by intro q hq; simpa using hq
  train_iff := fun _ _ _ => Iff.rfl

/-- The train-reflection and selected-label clauses compose along the pass. -/
def TransitionEmbedding.comp
    {S T R : ForestStage A B D family t targetTrain allowed}
    (g : TransitionEmbedding T R) (f : TransitionEmbedding S T) :
    TransitionEmbedding S R where
  toPartite := g.toPartite.comp f.toPartite
  map_selected := by
    intro q hq
    exact g.map_selected (mapDesignated f.toPartite q) (f.map_selected q hq)
  train_iff := by
    intro μ a₁ a₂
    exact (g.train_iff μ (f.toPartite.toEmbedding.comp a₁)
      (f.toPartite.toEmbedding.comp a₂)).trans (f.train_iff μ a₁ a₂)

/-- Local homogeneous selection with the stronger transition map. -/
def PictureStep
    (S T : ForestStage A B D family t targetTrain allowed)
    (α : UA ↪ P) (κ : Type w) : Prop :=
  ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A T.system α → κ,
    ∃ f : TransitionEmbedding S T,
      ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        χ (e₁.comp f.toPartite) = χ (e₂.comp f.toPartite)

/-- Forgetting selected labels and train reflection gives the usual property.
The reverse implication is not assumed. -/
theorem PictureStep.pictureProperty
    {S T : ForestStage A B D family t targetTrain allowed}
    {α : UA ↪ P} {κ : Type w} (h : PictureStep S T α κ) :
    StructuralRamsey.Partite.PictureProperty A S.system α T.system κ := by
  intro χ
  obtain ⟨f, hf⟩ := h χ
  exact ⟨f.toPartite, hf⟩

/-- Simultaneous fibre homogeneity with selected-copy and train transport. -/
def CanonicalOn
    (S T : ForestStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) : Prop :=
  ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
    ∃ f : TransitionEmbedding S T, ∀ α ∈ profiles,
      ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        χ (f.toPartite.toEmbedding.comp e₁.val) =
          χ (f.toPartite.toEmbedding.comp e₂.val)

/-- Finite iteration with a stage-dependent invariant for the remaining
fibres.  `Ready` can record precisely the unprocessed-fibre refinability
needed by the larger-cutoff step; no arbitrary stage is assumed refinable.
-/
theorem ForestStage.finitePass
    (S : ForestStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestStage A B D family t targetTrain allowed,
      Ready [] T ∧ CanonicalOn S T profiles κ := by
  induction profiles generalizing S with
  | nil =>
      refine ⟨S, hReady, ?_⟩
      intro χ
      exact ⟨TransitionEmbedding.id S, fun α h => (List.not_mem_nil h).elim⟩
  | cons α profiles ih =>
      obtain ⟨R, hReadyR, hStep⟩ := step α profiles S hReady
      obtain ⟨T, hReadyT, hT⟩ := ih R hReadyR
      refine ⟨T, hReadyT, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hT χ
      obtain ⟨f, hf⟩ := hStep
        (fun e => χ (g.toPartite.toEmbedding.comp e.val))
      refine ⟨g.comp f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hf e₁ e₂
      · exact hg β hβ (e₁.comp f.toPartite) (e₂.comp f.toPartite)

/-- A covering finite list suffices for simultaneous homogeneity of all
projections.  `Ready` is retained through exactly the processed list.
-/
theorem ForestStage.allProjections
    (S : ForestStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestStage A B D family t targetTrain allowed,
      Ready [] T ∧
      ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
        ∃ f : TransitionEmbedding S T, ∀ α : UA ↪ P,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
            χ (f.toPartite.toEmbedding.comp e₁.val) =
              χ (f.toPartite.toEmbedding.comp e₂.val) := by
  obtain ⟨T, hReadyT, hT⟩ := ForestStage.finitePass
    S profiles κ Ready hReady step
  refine ⟨T, hReadyT, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hT χ
  exact ⟨f, fun α => hf α (hProfiles α)⟩

/-- The selected Ramsey arrow.  Strongness and the target train-restriction
law of the selected witness are available from the same returned stage. -/
def DesignatedArrow
    (S : ForestStage A B D family t targetTrain allowed) (κ : Type w) : Prop :=
  ∀ χ : RelStructure.Embedding A S.system.toRelStructure → κ,
    ∃ b : DesignatedCopy B D S.system family, b ∈ S.selected ∧
      ∀ a₁ a₂ : RelStructure.Embedding A B,
        χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)

theorem DesignatedArrow.arrow
    {S : ForestStage A B D family t targetTrain allowed} {κ : Type w}
    (h : DesignatedArrow S κ) :
    StructuralRamsey.Arrow A B S.system.toRelStructure κ := by
  intro χ
  obtain ⟨b, _, hb⟩ := h χ
  exact ⟨b.embedding, hb⟩

/-- The selected monochromatic copy has the required strongness and the
exact original train equivalences, including reflection at every level. -/
theorem DesignatedArrow.strongTrain
    {S : ForestStage A B D family t targetTrain allowed} {κ : Type w}
    (h : DesignatedArrow S κ)
    (χ : RelStructure.Embedding A S.system.toRelStructure → κ) :
    ∃ b : DesignatedCopy B D S.system family, b ∈ S.selected ∧
      AStrong A S.system.toRelStructure (copyCarrier b.embedding) ∧
      (∀ μ : Fin (t.length + 1), ∀ a₁ a₂ : RelStructure.Embedding A B,
        S.train.rel μ (actualEdge (b.embedding.comp a₁))
          (actualEdge (b.embedding.comp a₂)) ↔
        targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
      (∀ a₁ a₂ : RelStructure.Embedding A B,
        χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  obtain ⟨b, hb, hmono⟩ := h χ
  exact ⟨b, hb, S.strong b hb, S.targetRestriction b hb, hmono⟩

/-- Selected-copy extraction from a fully homogeneous pass, using only the
prescribed base-family arrow and actual selected lifts in the initial stage.
-/
theorem designatedArrow_of_canonicalOn
    (S T : ForestStage A B D family t targetTrain allowed)
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D S.system family, q ∈ S.selected ∧ q.base = b)
    (hCanon : ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
      ∃ f : TransitionEmbedding S T, ∀ α : UA ↪ P,
        ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
          χ (f.toPartite.toEmbedding.comp e₁.val) =
            χ (f.toPartite.toEmbedding.comp e₂.val)) :
    DesignatedArrow T κ := by
  classical
  intro χ
  obtain ⟨f, hf⟩ := hCanon χ
  let θ : RelStructure.Embedding A D → κ := fun α =>
    if hα : Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) then
      χ (f.toPartite.toEmbedding.comp (Classical.choice hα).val)
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ (α : RelStructure.Embedding A D)
      (e : StructuralRamsey.Partite.ProjectedEmbedding A S.system α) :
      θ α = χ (f.toPartite.toEmbedding.comp e.val) := by
    have he : Nonempty
        (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) := ⟨e⟩
    simp only [θ, dite_eq_left he]
    exact hf α.toFunctionEmbedding (Classical.choice he) e
  obtain ⟨b, hb, hmono⟩ := hBase θ
  obtain ⟨q, hq, hqb⟩ := hLift b hb
  subst b
  let projected (a : RelStructure.Embedding A B) :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system (q.base.comp a) :=
    ⟨q.lift.val.comp a, fun x => q.lift.property (a x)⟩
  refine ⟨mapDesignated f.toPartite q, f.map_selected q hq, ?_⟩
  intro a₁ a₂
  have h := hmono a₁ a₂
  rw [hθ (q.base.comp a₁) (projected a₁),
    hθ (q.base.comp a₂) (projected a₂)] at h
  exact h

/-- Conditional finite-pass assembly with a selected strong train Ramsey
arrow and all mixed-forest, parameter and tail invariants on the same output.
The local step consumes the precise remaining-fibre readiness invariant.
-/
theorem ForestStage.ramseyPass
    (S : ForestStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (Ready : List (UA ↪ P) →
      ForestStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D S.system family, q ∈ S.selected ∧ q.base = b)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestStage A B D family t targetTrain allowed,
      Ready [] T ∧ DesignatedArrow T κ := by
  obtain ⟨T, hReadyT, hT⟩ := ForestStage.allProjections
    S profiles κ Ready hReady hProfiles step
  exact ⟨T, hReadyT, designatedArrow_of_canonicalOn S T κ hBase hLift hT⟩

end Pass

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
