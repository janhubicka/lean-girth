import Girth.TrainCoverageFreeAttachment
import Girth.TrainActualCutoffTwoFromMixed
import Girth.ForestRecursiveOutputGirth
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual SAME-q finite F_t forest -> coverage-free attachment bounds

The original recursive ActiveAttachmentBounds required
IrreduciblesExtendTo A E, and even the mixed-core alternative
requires a selected ForestTailStage.mixedCoverage certificate.
Neither follows from the ARBITRARY circulation F_t witness at q=2.

The standalone coverage-free attachment requires only the true
physical A-support of the local core (nonempty, vertex-covering)
in addition to the original partite, selected-copy, train,
parameter and positive-cut inputs. The F_t train itself supplies
those physical support facts, NOT mixed irreducible coverage.

From one genuine finite mixed-SET forest through the SAME q,
derive the auxiliary attachment fields:
- genuine q-1 forest for q>2;
- ordinary core support girth >q for q>2;
- real full system girth >2 at universal TOP when q=2,
  not the false local bottom claim.

The last field follows from the checked q2 top classification,
provided physical support covers every vertex of the actual active
source; no new local F_t or output-girth oracle is introduced.

This is an actual standalone F_t bound adapter, conditional only on
the explicit local geometric/positive fields stated below.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

variable (stage : ForestStage A B D family t targetTrain allowed)
variable (hA : A.Irreducible) (e : Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce
    (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels
  (OldACarrierEdge A E.toRelStructure) t.length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => fun i : I => (f i).toEmbedding
local notation "Tested" => RelationalMixedSupportTest A RF
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I

/-- All auxiliary coverage-free attachment bounds from one SAME-q
F_t mixed finite-set forest and the genuine physical support of
the local core, without any IrreduciblesExtendTo or selected
mixed irreducible-cover premise. -/
theorem ActiveAttachmentBounds.of_sameVector_finiteMixed
    (hCorePartite : E.IsPartiteOver D)
    (hCoreSupportNonempty :
      Nonempty (OldACarrierEdge A E.toRelStructure))
    (hCoreSupportCovers : ∀ y : Y,
      ∃ edge : OldACarrierEdge A E.toRelStructure, y ∈ edge.1)
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
        e₀ ∈ supportCopies A
          (stage.system.induce S).toRelStructure ∧
        e₁ ∈ supportCopies A
          (stage.system.induce S).toRelStructure ∧
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
    ActiveAttachmentBounds stage hA e active E f U := by
  have hCoreGirth :
      GirthGT (supportCopies A E.toRelStructure)
        (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough
      (supportCopies A E.toRelStructure) Tested
      (t.headD 0) hForest
    rintro edge ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  refine {
    corePartite := hCorePartite
    coreSupportNonempty := hCoreSupportNonempty
    coreSupportCovers := hCoreSupportCovers
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
      intro X hX hCard
      exact hForest X hX (by omega)
  · exact activeGluingWitness_cutoffTwo_of_sameVectorMixed
      A stage.system e.toFunctionEmbedding E.toRelStructure
      RF U (t.headD 0) hForest

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
