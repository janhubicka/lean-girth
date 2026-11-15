import Girth.TrainSelectedPictureMixedStageAssembly
import Girth.TrainActualAttachmentBoundsFromFiniteMixed
import Girth.TrainActualSelectedMixedCoreAttachment

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual same-q finite F_t forest supplies MIXED-core attachment bounds

The original ActiveAttachmentBounds.of_sameVector_finiteMixed still asks
for the generally impossible at q=2 core IrreduciblesExtendTo A.
The weaker and genuinely sufficient ActiveAttachmentMixedBounds
requires only:
  * nonempty complete physical A-support of the local core;
  * every local core vertex in an ambient physical A-copy;
  * ORIGINAL selected B-or-A mixed irreducible coverage of the
    attached output, obtained from nested local selected-gluing
    mixed coverage and old selected B-or-A coverage.

The real selected lower ForestTailStage provides all three fields
without any external completion to A.

Everything ELSE is the same as the checked original constructor:
selected base strongness, two source A-edges of the OLD B target,
interior physical-train reflection, exact part parameters,
local mixed forests, positive local FullSystemGirthGT and
positive original output SupremeCycleBound.

This theorem derives the q-1 mixed forest (when q>2), the ordinary
core girth >q and the separate q=2 UNIVERSAL TOP system witness
from ONE genuine F_q finite-set forest. In particular it does not
falsely conclude local bottom FullSystemGirthGT 2.

With the true local selected F_t stage providing the mixed core
triple, this is the missing alternative input to the new actual
mixed-core stage and its literal selected Ramsey PictureStep.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

variable (stage : ForestTailStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) (e : Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce
    (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => fun i : I => (f i).toEmbedding
local notation "Tested" => RelationalMixedSupportTest A RF
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I

/-- Genuine same-q F_t FOREST data plus the three actual selected
lower-core fields construct the COMPLETE weaker attachment bounds.
There is no core IrreduciblesExtendTo A premise; all remaining
non-forest local fields remain explicitly named and checkable. -/
theorem ActiveAttachmentMixedBounds.of_sameVector_finiteMixed
    (hCorePartite : E.IsPartiteOver D)
    (hCoreTriple :
      Nonempty (OldACarrierEdge A E.toRelStructure) ∧
      (∀ y : Y, ∃ edge : OldACarrierEdge A E.toRelStructure,
        y ∈ edge.1) ∧
      SelectedBorACoversIrreducibles A B D
        (StructuralRamsey.Partite.Attachment.attach stage.system S E f)
        family (transportedSelectedCopies B D stage.system
          family stage.selected S E f))
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
    (hSelectedSupports : Function.Injective
      (fun i : I => bSupportPiece A (RF i)))
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
    ActiveAttachmentMixedBounds stage hA e active E f U := by
  have hCoreGirth :
      GirthGT (supportCopies A E.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough
      (supportCopies A E.toRelStructure) Tested
      (t.headD 0) hForest
    rintro edge ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  refine {
    corePartite := hCorePartite
    coreSupportNonempty := hCoreTriple.1
    coreSupportCovers := hCoreTriple.2.1
    coreMixedCoverage := hCoreTriple.2.2
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
      refine Or.inr ⟨hSourceTwo hGt, hSelectedSupports, ?_⟩
      intro T hT hCard
      exact hForest T hT (by omega)
  · exact ActiveAttachmentBounds.cutoffTwo_of_finiteMixed
      stage e E f U hForest

end StructuralRamsey.Girth.TrainRecursiveWitness
