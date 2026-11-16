import Girth.TrainCoverageFreeNontrivialFtStep
import Girth.TrainCoverageFreeExactLocalTrain
import Girth.TrainRecursiveActivePartite
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Direct F_t partite witness -> coverage-free local picture step

This is the direct route from the forest assertion: its witness is
A-partite using the processed active A-fine predicates, and need
NOT be represented by a selected stage over an auxiliary large
Ramsey base. The larger-base coarsening modules are reusable for
recursive lower stages, but such a stage is not an additional
premise of the ABSTRACT F_t assertion.

Given raw F_t data PLUS the strong ordered-partiteness premise on the
true induced active target, relabel
the part map along the processed base A-copy, use the genuine
selected train-embedding law for exact original shared-edge
relations, and reuse the SAME-vector forest-to-order attachment.

This theorem is source-only and has NOT been elaborated by Lean.
The external inputs are the raw F_t data; this module does not
yet prove their existence from a formally stated abstract F_t
principle.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}

variable (A₀ : RelStructure L UA)
variable [LinearOrder UA] [Finite UA] [Nontrivial UA]
local notation "A" => A₀.ordered

variable {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section RawLocalFt

variable (stage : ForestStage A B D family (q :: tail) targetTrain allowed)
variable (hBaseLinear : ALinear A D)
variable (e : Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (H : StructuralRamsey.Partite.System L.withOrder UA Y)
variable [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding) H)
variable (U : EdgeTrainLevels
  (OldACarrierEdge A H.toRelStructure) (q :: tail).length)

local notation "S" =>
  activeCarrier A stage.system e.toFunctionEmbedding
local notation "Target" =>
  actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
local notation "Core" => H.relabel e.toFunctionEmbedding
local notation "F" =>
  (fun i : I =>
    activePartiteToRelabelledCore
      A stage.system e.toFunctionEmbedding H (f i))
local notation "RF" =>
  (fun i : I => (F i).toEmbedding)

/-- The raw forest assertion yields the actual selected next
OrderStage/PictureStep, with no extra recursive mixedCoverage.
The exact lower train law and the positive FULL local bounds are
literal fields of F_t, not inferred from ordinary wagon girth. -/
theorem ForestStage.orderPictureStep_of_rawPartiteFt
    (hReady : stage.BottomReady)
    (hBaseCovered : stage.CoversBase)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hPartite : H.IsPartiteOver A)
    (hSupportNonempty : Nonempty (OldACarrierEdge A H.toRelStructure))
    (hSupportCovers : ∀ y : Y,
      ∃ edge : OldACarrierEdge A H.toRelStructure, y ∈ edge.1)
    (hSelectedSupports : Function.Injective
      (fun i : I => bSupportPiece A ((f i).toEmbedding)))
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun i : I => (f i).toEmbedding)) q)
    (hSelectedTrain :
      ∀ (μ : Fin ((q :: tail).length + 1)) (i : I)
        (a b : Embedding A Target.toRelStructure),
        U.rel μ
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        (((stage.train.restrict
          (sharedOldACarrierInclusion A stage.system.toRelStructure S)).restrict
          (inducedACarrierToShared A stage.system.toRelStructure S)).rel μ)
            (actualEdge a) (actualEdge b))
    (hFineParameters : U.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => H.part ⁻¹' (e.toFunctionEmbedding ⁻¹' allowed ν)))
    (hPositive :
      ∀ j : Fin (q :: tail).length, 0 < j.val →
        (activeGluingWitnessOrderOneData A stage.system
          e.toFunctionEmbedding H.toRelStructure
          (fun i : I => (f i).toEmbedding) U j.castSucc)
          .FullSystemGirthGT ((q :: tail).get j))
    (κ : Type w) [Nonempty κ]
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A H.toRelStructure → κ,
        ∃ i : I,
          ∀ a b : Embedding A Target.toRelStructure,
            χ (actualEdge ((f i).toEmbedding.comp a)) =
              χ (actualEdge ((f i).toEmbedding.comp b))) :
    ∃ next : OrderStage A B D family (q :: tail)
      targetTrain allowed,
      PictureStep stage next.toForestStage
        e.toFunctionEmbedding κ := by
  have hA : A.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid : ∀ a : Embedding A D,
      SameCopy a e → a = e :=
    fun a ha => ordered_embedding_eq_of_sameCopy a e ha
  have hCorePartite : Core.IsPartiteOver D := by
    change H.toRelStructure.IsHomomorphismEmbedding
      D (e.toFunctionEmbedding ∘ H.part)
    exact e.isHomomorphismEmbedding.comp hPartite
  have hInterior : ∀ μ : Fin ((q :: tail).length + 1),
      0 < μ.val → μ.val < (q :: tail).length →
      ∀ (i : I)
        (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
        stage.train.rel μ p.1 r.1 ↔
          U.rel μ
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S Core.toRelStructure RF i p)
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S Core.toRelStructure RF i r) := by
    intro μ _hPos _hLt i p r
    exact originalSharedTrain_iff_of_selectedFt_embeddings
      A stage.system.toRelStructure S Core.toRelStructure RF
      stage.train U hSelectedTrain μ i p r
  have hCoreParameters : U.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => Core.part ⁻¹' allowed ν) := by
    change U.AdjacentParameters (fun edge => edge.1)
      (fun ν => H.part ⁻¹' (e.toFunctionEmbedding ⁻¹' allowed ν))
    exact hFineParameters
  have hCarrierRigid : ∀ a b : Embedding A Core.toRelStructure,
      SameCopy a b → a = b :=
    fun a b hab => ordered_embedding_eq_of_sameCopy a b hab
  exact stage.orderPictureStep_of_nontrivial_Ft
    hA hBaseLinear e hRigid active Core F U
    hBaseCovered hSelectedStrong hTargetTwo hCutoff
    hInterior hPositive
    hReady hPair hCorePartite
    hSupportNonempty hSupportCovers
    hSelectedSupports hForest hCoreParameters
    κ hCarrierRigid hPhysicalArrow

end RawLocalFt

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
