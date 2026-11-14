import Girth.TrainActualCutoffTwoFromMixed
import Girth.TrainActualWitnessBottomMixedForestBridge
import Girth.TrainSelectedPictureStageAssembly
import Girth.ForestRecursiveOutputGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# Real same-vector F_t data supply the auxiliary attachment bounds

The existing finite stage constructor ActiveAttachmentBounds requests
three auxiliary local certificates in addition to its actual
prescribed partite, selected-copy and positive-cut data:

(1) a local mixed forest through q-1 when q>2;
(2) ordinary local core A-support girth strictly above q when q>2;
(3) an extra local FullSystemGirthGT 2 witness when q=2.

ALL THREE follow from ONE genuine finite-SET mixed forest through
the SAME q, using the checked smaller-family restriction, ordinary
girth-from-mixed-forest theorem, and the new universal-top
order-two full-system lemma. In particular, q=2 does not require
incorrectly promoting bottom local forests to bottom system girth.

The remaining fields of ActiveAttachmentBounds are genuine
partite-geometry, selected-base, exact interior-train, full
positive-cut, and tail-supreme data. These must be produced by the
actual F_t witness and old picture; this constructor does not
postulate their existence.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

section RealMixedBounds

variable (stage : ForestTailStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) (e : Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "Tested" => RelationalMixedSupportTest A RF
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I

/-- The exact attachment structure follows from the genuine local
finite-set mixed forest THROUGH q and the actual remaining
geometric/positive-cut F_t fields. Its core-girth, smaller local
forest and cutoff-two full witness fields are all PROVED, rather
than supplied as independent hypotheses. The local family is
chosen with one complete support copy per vertex image. -/
theorem ActiveAttachmentBounds.of_sameVector_finiteMixed
    (hCorePartite : E.IsPartiteOver D)
    (hCoreCoverage : RelStructure.IrreduciblesExtendTo A E.toRelStructure)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family,
      b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hInterior : ∀ μ : Fin (t.length + 1),
      0 < μ.val → μ.val < t.length →
      ∀ (i : I) (p q : SharedOldACarrierEdge A stage.system.toRelStructure S),
        stage.train.rel μ p.1 q.1 ↔
        U.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i p)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i q))
    (hq : 2 ≤ t.headD 0)
    (hSourceTwo : 2 < t.headD 0 →
      ∃ e₀ e₁ : Set S,
        e₀ ∈ supportCopies A (stage.system.induce S).toRelStructure ∧
        e₁ ∈ supportCopies A (stage.system.induce S).toRelStructure ∧
        e₀ ≠ e₁)
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hForest : FiniteMixedForestThrough Tested (t.headD 0))
    (hCoreParameters : U.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => E.part ⁻¹' allowed ν))
    (hInteriorFull : ∀ μ : Fin (t.length + 1),
      0 < μ.val → μ.val < t.length →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U μ)
        .FullSystemGirthGT 2)
    (hTailSupreme : ∀ j : Fin t.length, 0 < j.val →
      (attachedSelectedPictureOrderOneData A hA B D stage.system
        family stage.selected e E.toRelStructure RF stage.train U
        Shared j.castSucc).SupremeCycleBound (t.get j)) :
    ActiveAttachmentBounds stage hA e active E f U := by
  have hCoreGirth : GirthGT (supportCopies A E.toRelStructure)
      (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough
      (supportCopies A E.toRelStructure) Tested
      (t.headD 0) hForest
    rintro edge ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  have hSupportsDistinct :
      Function.Injective (fun i => bSupportPiece A (RF i)) :=
    activeGluingWitness_supportPiece_injective_of_distinct_images
      A stage.system e.toFunctionEmbedding E.toRelStructure RF
      hSelectedImages
  refine {
    corePartite := hCorePartite
    coreCoverage := hCoreCoverage
    baseStrong := hBaseStrong
    targetTwo := hTargetTwo
    interior := hInterior
    bottomTwo := hq
    localForest := ?_
    coreGirth := fun _ => hCoreGirth
    cutoffTwo := ?_
    coreParameters := hCoreParameters
    interiorFull := hInteriorFull
    tailSupreme := hTailSupreme
  }
  · by_cases hTwo : t.headD 0 = 2
    · exact Or.inl hTwo
    · have hGt : 2 < t.headD 0 := by omega
      refine Or.inr ⟨hSourceTwo hGt, hSupportsDistinct, ?_⟩
      intro s hs hCard
      exact hForest s hs (by omega)
  · exact ActiveAttachmentBounds.cutoffTwo_of_finiteMixed
      stage e E f U hForest

end RealMixedBounds
end StructuralRamsey.Girth.TrainRecursiveWitness
