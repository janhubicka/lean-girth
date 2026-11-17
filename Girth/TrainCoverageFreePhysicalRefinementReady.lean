import Girth.TrainCoverageFreePhysicalAttachment
import Girth.TrainCoverageFreePhysicalUntouchedRefinement
import Girth.TrainSelectedPictureRefinementReady

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every remaining profile admits a first-wagon refinement on its
complete physical support. -/
def PhysicalForestStage.FirstRefinementReady
    {A : RelStructure L.withOrder UA}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    (ht : 0 < t.length) (g : ℕ) (profiles : List (UA ↪ P))
    (stage : PhysicalForestStage A B D family t targetTrain allowed) : Prop :=
  RemainingFirstRefinable A stage.system stage.train ht
    (allowed ⟨1, Nat.succ_lt_succ ht⟩) g profiles

theorem PhysicalForestStage.FirstRefinementReady.tail
    {A : RelStructure L.withOrder UA}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {ht : 0 < t.length} {g : ℕ} {α : UA ↪ P} {profiles : List (UA ↪ P)}
    {stage : PhysicalForestStage A B D family t targetTrain allowed}
    (hReady : PhysicalForestStage.FirstRefinementReady ht g (α :: profiles) stage) :
    PhysicalForestStage.FirstRefinementReady ht g profiles stage :=
  RemainingFirstRefinable.tail hReady

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
variable (stage : PhysicalForestStage A₀.ordered B D family t targetTrain allowed)
variable (hBaseLinear : ALinear A₀.ordered D) (e : Embedding A₀.ordered D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A₀.ordered stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L.withOrder P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A₀.ordered E.toRelStructure) t.length)
variable (bounds : ActiveAttachmentBounds stage
  (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible e active E f U)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Rigid" => fun a h => ordered_embedding_eq_of_sameCopy a e h
local notation "Next" => PhysicalForestStage.activeAttachment_of_bounds
  stage hA hBaseLinear e Rigid active E f U bounds

/-- One genuine physical attachment preserves readiness of every
unprocessed fibre by appending a refinement level. -/
theorem PhysicalForestStage.activeAttachment_firstRefinementReady
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier e)
    (ht : 0 < t.length) (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : PhysicalForestStage.FirstRefinementReady ht (t.headD 0 - 1)
      (e.toFunctionEmbedding :: remaining) stage) :
    PhysicalForestStage.FirstRefinementReady ht (t.headD 0 - 1) remaining (Next) := by
  classical
  have hRel := sharedSupportTrainRel_of_interior stage.train U
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure S E.toRelStructure RF)
    (fun μ hZero hTop i a b => bounds.interior μ (by omega) (by omega) i a b)
  have hLocal : LocalForestThrough (fun i => bSupportPiece A (f i).toEmbedding)
      (t.headD 0 - 1) := by
    rcases bounds.localForest with hTwo | ⟨_, hInjective, hMixed⟩
    · rw [hTwo]
      exact actualRecursiveLocalForest_one _
    · exact FiniteMixedForestThrough.toLocalForestThrough _ hInjective
        (RelationalMixedSupportTest A RF) (t.headD 0 - 1)
        (fun i => Or.inl ⟨i, rfl⟩) hMixed
  intro β hβ
  by_cases hBase : ∃ b : Embedding A D, b.toFunctionEmbedding = β
  · obtain ⟨b, rfl⟩ := hBase
    have hDifferent : e ≠ b := by
      intro h
      subst b
      exact hFresh hβ
    obtain ⟨R⟩ := hReady b.toFunctionEmbedding (List.mem_cons_of_mem _ hβ)
    exact ⟨untouchedActiveFirstWagonRefinement_of_projectsACopies A₀ D stage.system e b E f
      stage.train U Shared stage.projectsACopies bounds.coreProjectsACopies
      hBaseLinear hDifferent hCoreSupport hRel ht allowed (Next).parameters
      (t.headD 0 - 1) hLocal R⟩
  · apply activeFirstRefinable_of_empty_activeCarrier A (Next).system (Next).train
      ht (allowed ⟨1, Nat.succ_lt_succ ht⟩) (t.headD 0 - 1) β
    rintro ⟨x, a, _u, _hVertex⟩
    exact hBase (baseEmbedding_of_projectedACopy A D (Next).system (Next).projectsACopies β a)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
