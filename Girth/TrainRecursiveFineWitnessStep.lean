import Girth.TrainRecursiveFineWitnessBounds
import Girth.TrainRecursiveActivePartite

set_option autoImplicit false
set_option Elab.async false

/-!
# The ordered refining picture step from intrinsic fine-witness data

The actual A-partite fine witness supplies the coarse attachment bounds
through `activeAttachmentBounds_of_fineWitness`.  Its partite family arrow
then constructs the next finite stage and its picture step.  Freshness of
the processed profile preserves first-refinement readiness on every
remaining profile, using the complete active supports.

No completed attachment-bound record or next stage is an input.  The
fine witness, its Ramsey arrow, and the indexed supreme-cycle bound of
the attached output remain explicit inputs.  This covers the bottom
cutoff greater than two and makes no witness-existence assertion.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
variable {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (stage : ForestTailStage A₀.ordered B D family t targetTrain allowed)
variable (hBaseLinear : ALinear A₀.ordered D) (e : Embedding A₀.ordered D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A₀.ordered stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L.withOrder UA Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding) E)
variable (ht : 0 < t.length) (hq : 2 < t.headD 0)
variable (R : FirstWagonRefinement
  (stage.train.restrict (sharedOldACarrierInclusion A₀.ordered stage.system.toRelStructure
    (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding)))
  ht (fun edge => edge.1.1) stage.system.part
  (allowed ⟨1, Nat.succ_lt_succ ht⟩) (t.headD 0 - 1))
variable (T : EdgeTrainLevels (OldACarrierEdge A₀.ordered E.toRelStructure)
  (t.length + R.extraCuts))
variable (fineAllowed : Fin (t.length + R.extraCuts + 1) → Set UA)
variable (hPartite : E.IsPartiteOver A₀.ordered)
variable (hCoverage : IrreduciblesExtendTo A₀.ordered E.toRelStructure)
variable (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family, b ∈ stage.selected →
  AStrong A₀.ordered D (copyCarrier b.base))
variable (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
variable (hActiveTwo : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
  A₀.ordered stage.system e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
variable (hPhysicalInjective :
  Function.Injective (fun i => bSupportPiece A₀.ordered (f i).toEmbedding))
variable (hForest : FiniteMixedForestThrough
  (RelationalMixedSupportTest A₀.ordered (fun i => (f i).toEmbedding)) (t.headD 0 - 1))
variable (hRestriction : ∀ (ν : Fin (t.length + R.extraCuts + 1)) (i : I)
  (a b : Embedding A₀.ordered (stage.system.toRelStructure.induce
    (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding))),
  T.rel ν (actualEdge ((f i).toEmbedding.comp a)) (actualEdge ((f i).toEmbedding.comp b)) ↔
    (R.train.restrict (inducedACarrierToShared A₀.ordered stage.system.toRelStructure
      (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding))).rel ν
      (actualEdge a) (actualEdge b))
variable (hParameters : T.AdjacentParameters (fun edge => edge.1)
  (fun ν => E.part ⁻¹' fineAllowed ν))
variable (hSingleton : ∀ j : Fin (R.extraCuts + 1),
  (fineAllowed (firstRefinementParent t.length R.extraCuts ht j)).Subsingleton)
variable (hFirst : ∀ ρ : Fin (t.length + R.extraCuts + 1), 0 < ρ.val →
  ρ.val ≤ R.extraCuts + 1 →
  fineAllowed ρ ⊆ e.toFunctionEmbedding ⁻¹' allowed ⟨1, Nat.succ_lt_succ ht⟩)
variable (hRetained : ∀ ν : Fin (t.length + 1), 0 < ν.val →
  fineAllowed (EdgeTrainLevels.firstForgetIndex t.length R.extraCuts ν) ⊆
    e.toFunctionEmbedding ⁻¹' allowed ν)
variable (hFull : ∀ ν : Fin (t.length + R.extraCuts + 1), 0 < ν.val →
  ν.val < t.length + R.extraCuts →
  (activeGluingWitnessOrderOneData A₀.ordered stage.system e.toFunctionEmbedding E.toRelStructure
    (fun i => (f i).toEmbedding) T ν).FullSystemGirthGT
      (if ν.val ≤ R.extraCuts then t.headD 0 - 1 else t.headD 0))
variable (hTail : ∀ j : Fin t.length, 0 < j.val →
  (attachedSelectedPictureOrderOneData A₀.ordered
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    B D stage.system family stage.selected
    e E.toRelStructure (fun i => (f i).toEmbedding) stage.train (T.forgetFirstCuts ht)
    (activeCarrier_all_standard_copies_meet_core
      A₀.ordered stage.system e.toFunctionEmbedding active I) j.castSucc).SupremeCycleBound (t.get j))

local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

include hBaseLinear hq hPartite hCoverage hBaseStrong hTargetTwo hActiveTwo
  hPhysicalInjective hForest hRestriction hParameters hSingleton hFirst hRetained hFull hTail

/-- Intrinsic fine-witness data construct an actual ordered picture step
whose next stage retains first-refinement readiness on all fresh remaining
profiles.  The coarse attachment bounds are derived inside the proof. -/
theorem ForestTailStage.refiningPictureStep_of_fineWitness
    (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1)
      (e.toFunctionEmbedding :: remaining) stage)
    (κ : Type w)
    (hArrow : ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) E → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding),
        χ ((f i).comp a) = χ ((f i).comp b)) :
    ∃ next : ForestTailStage A B D family t targetTrain allowed,
      ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1) remaining next ∧
      PictureStep stage next e.toFunctionEmbedding κ := by
  let bounds := stage.activeAttachmentBounds_of_fineWitness hA e active E f ht hq
    R T fineAllowed hPartite hCoverage hBaseStrong hTargetTwo hActiveTwo
    hPhysicalInjective hForest hRestriction hParameters hSingleton hFirst hRetained hFull hTail
  exact ⟨_, stage.activeAttachment_refiningPictureStep_of_partiteFamilyArrow
    A₀ hBaseLinear e active E f (T.forgetFirstCuts ht) bounds
    ht remaining hFresh hReady κ hArrow⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
