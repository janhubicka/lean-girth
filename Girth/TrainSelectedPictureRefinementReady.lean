import Girth.TrainUntouchedRefinement
import Girth.TrainSelectedPictureStageAssembly
import Girth.TrainRecursiveRefinementReady
import Girth.TrainRecursiveWitnessProfiles

set_option Elab.async false
set_option autoImplicit false

/-!
# Refinement readiness of the actual selected picture step

The next stage is the literal attachment already constructed from the
intrinsic local bounds.  Its complete remaining active supports inherit
the appended refinements.  Freshness excludes the processed profile from
the remaining list.  A profile which does not come from a base embedding
has empty active carrier and receives the matching refinement directly.

The additional support input says that every core vertex lies over the
processed base copy.  Local predecessor foresthood is derived from the
stage bounds, including the automatic one-member case at bottom cutoff
two.  No completed next-stage refinement or ready-step operator is assumed.
Local witness existence and global supreme-cycle transfer remain separate.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

/-- An empty active vertex carrier has at most one physical support edge,
even when the source itself is empty.  Its matching refinement is actual
data and requires no base embedding for the profile. -/
theorem activeFirstRefinable_of_empty_activeCarrier
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (hm : 0 < m) (firstAllowed : Set P) (g : ℕ) (β : UA ↪ P)
    (hEmpty : ¬ (activeCarrier A C β).Nonempty) :
    ActiveFirstRefinable A C T hm firstAllowed g β := by
  have hEdge (a : SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C β)) :
      a.1.1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hEmpty ⟨x, a.2 hx⟩
  refine ⟨firstWagonRefinement_of_matching
    (T.restrict (sharedOldACarrierInclusion A C.toRelStructure (activeCarrier A C β)))
    hm (fun a => a.1.1) ?_ C.part firstAllowed g 0⟩
  intro a b hab
  exact (hab (Subtype.ext (Subtype.ext ((hEdge a).trans (hEdge b).symm)))).elim

section Stage

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)
variable {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (stage : ForestTailStage A₀.ordered B D family t targetTrain allowed)
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
local notation "Next" => stage.activeAttachment_of_local_bounds
  hA hBaseLinear e Rigid active E f U bounds

omit [Finite UA] [Finite Y] [Finite I] in
include bounds in
/-- The local bounds already supply the indexed forest at the predecessor
cutoff.  At cutoff two this is the automatic one-member forest. -/
theorem ActiveAttachmentBounds.localForest_predecessor :
    LocalForestThrough (fun i => bSupportPiece A (f i).toEmbedding) (t.headD 0 - 1) := by
  rcases bounds.localForest with hTwo | ⟨_, hInjective, hMixed⟩
  · rw [hTwo]
    exact actualRecursiveLocalForest_one _
  · exact FiniteMixedForestThrough.toLocalForestThrough _ hInjective
      (RelationalMixedSupportTest A RF) (t.headD 0 - 1)
      (fun i => Or.inl ⟨i, rfl⟩) hMixed

/-- Every remaining profile has a complete actual first-wagon refinement
after the attachment.  The processed profile is excluded by freshness;
non-base profiles are handled through their empty active support. -/
theorem ForestTailStage.activeAttachment_firstRefinementReady
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier e)
    (ht : 0 < t.length) (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1)
      (e.toFunctionEmbedding :: remaining) stage) :
    ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1) remaining (Next) := by
  classical
  have hRel := sharedSupportTrainRel_of_interior stage.train U
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure S E.toRelStructure RF)
    (fun μ hZero hTop i a b => bounds.interior μ (by omega) (by omega) i a b)
  intro β hβ
  by_cases hBase : ∃ b : Embedding A D, b.toFunctionEmbedding = β
  · obtain ⟨b, rfl⟩ := hBase
    have hDifferent : e ≠ b := by
      intro h
      subst b
      exact hFresh hβ
    obtain ⟨R⟩ := hReady b.toFunctionEmbedding (List.mem_cons_of_mem _ hβ)
    exact ⟨untouchedActiveFirstWagonRefinement A₀ D stage.system e b E f
      stage.train U Shared stage.isPartite bounds.corePartite
      hBaseLinear hDifferent hCoreSupport hRel ht allowed (Next).parameters
      (t.headD 0 - 1) (bounds.localForest_predecessor A₀ stage e active E f U) R⟩
  · apply activeFirstRefinable_of_empty_activeCarrier A (Next).system (Next).train
      ht (allowed ⟨1, Nat.succ_lt_succ ht⟩) (t.headD 0 - 1) β
    intro hActive
    obtain ⟨b, hb, _⟩ := baseEmbedding_of_nonempty_activeCarrier
      A D (Next).system hA (Next).isPartite β hActive
    exact hBase ⟨b, hb⟩

/-- The ordinary local Ramsey arrow now gives the actual selected picture
step together with preservation of the concrete remaining-fibre readiness
invariant.  Its local witness and supreme-cycle inputs remain explicit. -/
theorem ForestTailStage.activeAttachment_refiningPictureStep_of_familyArrow
    (hCoreSupport : ∀ y : Y, E.part y ∈ copyCarrier e)
    (ht : 0 < t.length) (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1)
      (e.toFunctionEmbedding :: remaining) stage)
    (κ : Type w) [Nonempty κ]
    (hArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A (stage.system.induce S).toRelStructure,
        χ ((f i).toEmbedding.comp a) = χ ((f i).toEmbedding.comp b)) :
    ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1) remaining (Next) ∧
      PictureStep stage (Next) e.toFunctionEmbedding κ := by
  exact ⟨stage.activeAttachment_firstRefinementReady A₀ hBaseLinear e active E f U bounds
      hCoreSupport ht remaining hFresh hReady,
    stage.activeAttachment_pictureStep_of_familyArrow hA hBaseLinear e Rigid active E f U
      bounds κ hArrow⟩

end Stage
end StructuralRamsey.Girth.TrainRecursiveWitness
