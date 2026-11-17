import Girth.TrainCoverageFreePhysicalOrderPass
import Girth.TrainCoverageFreeACopyProjection
import Girth.TrainRecursiveNontrivialFibre
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Coverage-free finite pass: identity on singleton physical fibres

The checked ordered physical-fibre dispatch never uses
ForestTailStage.mixedCoverage. The same exact proof therefore
works for CoverageFree.PhysicalForestStage:

* Empty or singleton physical projected A-fibres use the literal
  identity selected train transition, preserving all data.
* A nontrivial physical fibre supplies two different projected
  A-copy image carriers and a genuine base embedding of A; only
  this case requires an actual local F_t picture step.

No one-edge degenerate attachment or new witness is used.
The proof is a structural port of the checked original finite
pass and retains the selected-family train reflection.
-/

/-!
Weak physical-stage fibre dispatch. Source proof is the checked
identity/nontrivial case split, with ONLY the base-embedding bridge
weakened from full IsPartiteOver to ProjectsACopies. No local F_t
witness is assumed in the empty/singleton case. Uncompiled.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA}
variable {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

theorem pictureStep_self_of_subsingleton_physical_fibre
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (B : RelStructure L.withOrder VB) (D : RelStructure L.withOrder P)
    (family : Set (RelStructure.Embedding B D)) (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (S : PhysicalForestStage A₀.ordered B D family t targetTrain allowed)
    (α : UA ↪ P) (κ : Type w)
    (hPhysical : (Set.range (fun e :
      StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered S.system α =>
        copyCarrier e.val)).Subsingleton) :
    PictureStep S S α κ := by
  intro χ
  refine ⟨TransitionEmbedding.id S, ?_⟩
  intro e₁ e₂
  have hSame : SameCopy e₁.val e₂.val :=
    hPhysical ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
  have hEq : e₁ = e₂ :=
    Subtype.ext (ordered_embedding_eq_of_sameCopy e₁.val e₂.val hSame)
  rw [hEq]



section Ordered

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

theorem PhysicalForestStage.profileStep_of_nontrivialStep
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    (S : PhysicalForestStage A B D family t targetTrain allowed)
    (α : UA ↪ P) (remaining : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      PhysicalForestStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready (α :: remaining) S)
    (hSkipReady : (Set.range (fun a :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system α =>
        copyCarrier a.val)).Subsingleton → Ready remaining S)
    (actualStep : ∀ e : Embedding A D,
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : PhysicalForestStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : PhysicalForestStage A B D family t targetTrain allowed,
      Ready remaining T ∧ PictureStep S T α κ := by
  classical
  by_cases hPhysical : (Set.range (fun a :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system α =>
        copyCarrier a.val)).Subsingleton
  · exact ⟨S, hSkipReady hPhysical,
      pictureStep_self_of_subsingleton_physical_fibre
        A₀ B D family t targetTrain allowed S α κ hPhysical⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hPhysical
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        copyCarrier a.val ≠ copyCarrier b.val := ⟨a, b, hxy⟩
    obtain ⟨e, he⟩ := baseEmbedding_of_projectedACopy
      A D S.system S.projectsACopies α a
    subst α
    exact actualStep e hPair hReady


end Ordered
end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
