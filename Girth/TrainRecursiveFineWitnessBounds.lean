import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveFineWitnessSystemGirth
import Girth.TrainRecursiveBottomEqualityBridge
import Girth.TrainRecursiveRefinementGlobalCutGirth
import Girth.TrainRecursiveNontrivialFibre

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual attachment bounds from an A-partite fine witness

For the branch whose bottom cutoff is greater than two, the fine local
witness supplies its own mixed forest, train restriction, adjacent
parameters and positive full-system bounds.  These data construct the
coarse attachment bounds; none of the coarse compatibility, parameter,
interior-system or core-girth conclusions is an input.

If the refinement inserts `d` extra cuts, positive child cuts through `d`
need cutoff `q - 1`.  Retained nonterminal cuts need cutoff at least `q`.
This is the lower bound supplied by the recursive vector
`replicate (d + 1) (q - 1) ++ tail` when `q :: tail` is admissible.
Bottom girth comes from the mixed forest, with no bottom system-girth
assumption.  The retained first cut gives global core girth `> q`; when
the tail is empty, that cut is the universal top instead.

The local finite witness and its Ramsey arrow still have to be obtained
from the induction hypothesis.  The indexed supreme-cycle bound for the
attached output remains an explicit, separate premise.  The cutoff-two
branch is not handled by this construction.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- Intrinsic fine geometry and the actual gluing-system bounds give
ordinary girth of the entire local core.  The refinement is constructed
from adjacent parameters and singleton fine parts.  No selected-picture
incidence record is substituted for the actual prescribed gluing family.
-/
theorem activeFineWitness_supportGirth
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X) (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L UA Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (actualActiveSubsystemPartite A C α) E)
    {m d q : ℕ} (hm : 0 < m) (hq : 2 < q)
    (T : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (m + d))
    (fineAllowed : Fin (m + d + 1) → Set UA)
    (hParameters : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν))
    (hSingleton : ∀ j : Fin (d + 1),
      (fineAllowed (firstRefinementParent m d hm j)).Subsingleton)
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (q - 1))
    (hFull : ∀ ν : Fin (m + d + 1), 0 < ν.val → ν.val < m + d →
      (activeGluingWitnessOrderOneData A C α E.toRelStructure
        (fun i => (f i).toEmbedding) T ν).FullSystemGirthGT
          (if ν.val ≤ d then q - 1 else q)) :
    GirthGT (supportCopies A E.toRelStructure) q := by
  have hBottom : GirthGT (supportCopies A E.toRelStructure) (q - 1) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (q - 1) hForest
    rintro edge ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  let refinement : FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) E.part Set.univ (q - 1) :=
    FirstWagonRefinement.ofFineTrain T hm (fun edge => edge.1) E.part
      Set.univ (q - 1)
      (fun j => fineAllowed (firstRefinementParent m d hm j))
      (fun _ _ _ => Set.mem_univ _) hSingleton
      (fun j => hParameters (firstRefinementChild m d hm j)
        (firstRefinementParent m d hm j) (by change j.val ≤ j.val + 1; omega) rfl)
      (by
        intro j p
        apply T.labelledChildGirth_of_labelledCut (fun edge => edge.1)
          (firstRefinementChild m d hm j) (firstRefinementParent m d hm j)
          (by change j.val ≤ j.val + 1; omega) p (q - 1)
        by_cases hZero : j.val = 0
        · have hCut : firstRefinementChild m d hm j =
              (⟨0, Nat.zero_lt_succ (m + d)⟩ : Fin (m + d + 1)) :=
            Fin.ext hZero
          rw [hCut]
          exact T.bottom_labelledCutGirth_of_edgeGirth (fun edge => edge.1) (q - 1)
            (physicalASupport_labelledGirth_of_girth A E.toRelStructure (q - 1) hBottom)
        · have hPos : 0 < (firstRefinementChild m d hm j).val := by
            change 0 < j.val
            omega
          have hLt : (firstRefinementChild m d hm j).val < m + d := by
            change j.val < m + d
            have := j.isLt
            omega
          have hLe : (firstRefinementChild m d hm j).val ≤ d := by
            change j.val ≤ d
            have := j.isLt
            omega
          exact activeGluingWitness_labelledCutGirth_of_fullSystemGirth
            A C α E.toRelStructure (fun i => (f i).toEmbedding) T
            (firstRefinementChild m d hm j) (q - 1)
            (by simpa only [hLe, ↓reduceIte] using hFull _ hPos hLt))
  have hGain : GirthGT (supportCopies A E.toRelStructure) (q - 1 + 1) := by
    by_cases hOne : m = 1
    · apply refinement.actualSupport_girthGT_of_first_universal A hA E (by omega)
      intro a b
      have hTop : (⟨1, by omega⟩ : Fin (m + 1)) =
          ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hOne.symm
      rw [hTop]
      exact (T.forgetFirstCuts hm).top a b
    · apply refinement.actualSupport_girthGT_of_retainedFirstCut A hA E (by omega)
      let ν : Fin (m + d + 1) :=
        EdgeTrainLevels.firstForgetIndex m d ⟨1, Nat.succ_lt_succ hm⟩
      have hν : ν.val = d + 1 := by
        simp [ν, EdgeTrainLevels.firstForgetIndex, Nat.add_comm]
      have hCut := activeGluingWitness_labelledCutGirth_of_fullSystemGirth
        A C α E.toRelStructure (fun i => (f i).toEmbedding) T ν q
        (by
          have hNot : ¬ν.val ≤ d := by omega
          simpa only [hNot, ↓reduceIte] using hFull ν (by omega) (by omega))
      have hqEq : q - 1 + 1 = q := by omega
      rw [hqEq]
      exact hCut
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using hGain

section Attachment

variable {VB : Type v} {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (stage : ForestTailStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) (e : Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L UA Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding) E)
variable (ht : 0 < t.length) (hq : 2 < t.headD 0)
local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "Core" => E.relabel e.toFunctionEmbedding
local notation "F" => fun i : I =>
  activePartiteToRelabelledCore A stage.system e.toFunctionEmbedding E (f i)
local notation "RF" => fun i : I => StructuralRamsey.Partite.Embedding.toEmbedding (f i)
variable (R : FirstWagonRefinement
  (stage.train.restrict (sharedOldACarrierInclusion A stage.system.toRelStructure (activeCarrier A stage.system e.toFunctionEmbedding)))
  ht (fun edge => edge.1.1) stage.system.part
  (allowed ⟨1, Nat.succ_lt_succ ht⟩) (t.headD 0 - 1))
variable (T : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (t.length + R.extraCuts))
variable (fineAllowed : Fin (t.length + R.extraCuts + 1) → Set UA)
variable (hPartite : E.IsPartiteOver A)
variable (hCoverage : IrreduciblesExtendTo A E.toRelStructure)
variable (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family, b ∈ stage.selected →
  AStrong A D (copyCarrier b.base))
variable (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
variable (hActiveTwo : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
variable (hPhysicalInjective : Function.Injective (fun i => bSupportPiece A (f i).toEmbedding))
variable (hForest : FiniteMixedForestThrough (RelationalMixedSupportTest A (fun i : I => StructuralRamsey.Partite.Embedding.toEmbedding (f i))) (t.headD 0 - 1))
variable (hRestriction : ∀ (ν : Fin (t.length + R.extraCuts + 1)) (i : I)
  (a b : Embedding A (stage.system.toRelStructure.induce (activeCarrier A stage.system e.toFunctionEmbedding))),
  T.rel ν (actualEdge ((f i).toEmbedding.comp a)) (actualEdge ((f i).toEmbedding.comp b)) ↔
    (R.train.restrict (inducedACarrierToShared A stage.system.toRelStructure (activeCarrier A stage.system e.toFunctionEmbedding))).rel ν
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
  (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding E.toRelStructure
    (fun i : I => StructuralRamsey.Partite.Embedding.toEmbedding (f i)) T ν).FullSystemGirthGT (if ν.val ≤ R.extraCuts then t.headD 0 - 1 else t.headD 0))
variable (hTail : ∀ j : Fin t.length, 0 < j.val →
  (attachedSelectedPictureOrderOneData A hA B D stage.system family stage.selected
    e E.toRelStructure (fun i : I => StructuralRamsey.Partite.Embedding.toEmbedding (f i)) stage.train (T.forgetFirstCuts ht)
    (activeCarrier_all_standard_copies_meet_core
      A stage.system e.toFunctionEmbedding active I) j.castSucc).SupremeCycleBound (t.get j))

include hq hPartite hCoverage hBaseStrong hTargetTwo hActiveTwo hPhysicalInjective
  hForest hRestriction hParameters hSingleton hFirst hRetained hFull hTail

/-- Construct all actual coarse attachment bounds from intrinsic data of
the fine A-partite witness.  Source nontriviality is derived on the true
active subsystem.  Only the indexed output supreme-cycle bound remains
an output premise; the other assumptions concern the old stage or fine
witness. -/
theorem ForestTailStage.activeAttachmentBounds_of_fineWitness :
    ActiveAttachmentBounds stage hA e active (Core) (F) (T.forgetFirstCuts ht) := by
  refine {
    corePartite := StructuralRamsey.Partite.Induced.relabel_isPartiteOver
      (A := A) (B := E) hPartite e
    coreCoverage := hCoverage
    baseStrong := hBaseStrong
    targetTwo := hTargetTwo
    interior := ?_
    bottomTwo := by omega
    localForest := ?_
    coreGirth := ?_
    cutoffTwo := by intro h; omega
    coreParameters := relabelledCore_forgetFirstCuts_adjacentParameters
      A e.toFunctionEmbedding E T ht fineAllowed allowed hParameters hFirst hRetained
    interiorFull := ?_
    tailSupreme := hTail
  }
  · intro μ _ _ i p r
    exact coarseSharedTrain_iff_of_finePrescribedRestriction
      A stage.system.toRelStructure S E.toRelStructure RF
      stage.train ht R T hRestriction μ i p r
  · obtain ⟨a, b, hab⟩ := hActiveTwo
    obtain ⟨a', b', hne⟩ := activeSupport_two_distinct_of_projected_carriers
      A stage.system e.toFunctionEmbedding a b hab
    exact Or.inr ⟨⟨a'.1, b'.1, a'.2, b'.2, fun h => hne (Subtype.ext h)⟩,
      hPhysicalInjective, hForest⟩
  · intro _
    exact activeFineWitness_supportGirth A hA stage.system e.toFunctionEmbedding
      E f ht hq T fineAllowed hParameters hSingleton hForest hFull
  · apply activeGluingWitness_interiorFull_of_fine
      A stage.system e.toFunctionEmbedding E.toRelStructure RF T ht
    intro ν hPos hLt
    exact ⟨if ν.val ≤ R.extraCuts then t.headD 0 - 1 else t.headD 0,
      by split_ifs <;> omega, hFull ν hPos hLt⟩

/-- The fine witness and its partite family arrow produce an actual
selected picture step.  The next finite stage is built from the derived
bounds, so no completed stage or coarse attachment-bound record is an
assumption.  Ordering is needed only through the stated same-copy
rigidity of the processed base embedding. -/
theorem ForestTailStage.pictureStep_of_fineWitness
    [Finite UA] [Finite Y] [Finite I]
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (κ : Type w)
    (hArrow : ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) E → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding),
        χ ((f i).comp a) = χ ((f i).comp b)) :
    ∃ next : ForestTailStage A B D family t targetTrain allowed,
      PictureStep stage next e.toFunctionEmbedding κ := by
  let bounds := stage.activeAttachmentBounds_of_fineWitness hA e active E f ht hq
    R T fineAllowed hPartite hCoverage hBaseStrong hTargetTwo hActiveTwo
    hPhysicalInjective hForest hRestriction hParameters hSingleton hFirst hRetained hFull hTail
  refine ⟨stage.activeAttachment_of_local_bounds hA hBaseLinear e hRigid active
    (Core) (F) (T.forgetFirstCuts ht) bounds, ?_⟩
  apply stage.activeAttachment_pictureStep hA hBaseLinear e hRigid active
    (Core) (F) (T.forgetFirstCuts ht) bounds κ
  exact activeLocalSelection_of_partiteFamilyArrow A stage.system e.toFunctionEmbedding E f κ hArrow

end Attachment

end StructuralRamsey.Girth.TrainRecursiveWitness
