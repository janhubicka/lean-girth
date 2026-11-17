import Girth.TrainCoverageFreePhysicalOrderPass
import Girth.TrainCoverageFreeWeakProjectionGirth
import Girth.TrainRecursiveNontrivialFibre
import Girth.TrainActualOneLevelGirthIntrinsic
import Girth.TrainSharedSupportInteriorCompatibility
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Original positive-cut system girth without mixed irreducible coverage

The checked actual positive-cut source transfer uses only old full
system bounds, actual A-partiteness and base A-linearity/rigidity,
selected base strongness and two genuine A-copies of B, and local
positive full-system certificates. It does not inspect the old
stage's recursive mixedCoverage invariant.

This module reuses that theorem's body for the coverage-free stage.
The result is EXACT FullSystemGirthGT at every original proper
positive cut, preserving global simultaneous original B-labelled
supreme plans, not a weaker numerical order-one bound.

The local input remains a genuine F_t positive-cut witness. This
theorem alone neither constructs the physical F_t core nor
assumes output girth.
-/

/-!
Exact original B-labelled positive full-system bounds from
ProjectsACopies, old selected base lifts and the real local positive
witness. All simultaneous replacement plans are retained.
The proof is the original transfer with its sole stronger geometric
premise removed. UNCOMPILED SOURCE.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section PositiveFt
variable (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure)
  (q :: tail).length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => StructuralRamsey.Partite.Embedding.toEmbedding (f i))
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Out" => (fun μ : Fin ((q :: tail).length + 1) =>
  attachedSelectedPictureOrderOneData A hA B D stage.system
    family stage.selected e E.toRelStructure RF
    stage.train U Shared μ)

include hBaseLinear hRigid in
theorem PhysicalForestStage.actual_positive_full_of_Ft
    (hBaseCovered : stage.CoversBase)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hInterior : ∀ μ : Fin ((q :: tail).length + 1),
      0 < μ.val → μ.val < (q :: tail).length →
      ∀ (i : I) (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
        stage.train.rel μ p.1 r.1 ↔
          U.rel μ
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S E.toRelStructure RF i p)
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S E.toRelStructure RF i r))
    (hPositive : ∀ j : Fin (q :: tail).length, 0 < j.val →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U
        j.castSucc).FullSystemGirthGT ((q :: tail).get j)) :
    ∀ j : Fin (q :: tail).length, 0 < j.val →
      (Out j.castSucc).FullSystemGirthGT ((q :: tail).get j) := by
  have hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b) :=
    PhysicalForestStage.allBaseStrong_of_selected stage hBaseCovered hSelectedStrong
  obtain ⟨aB, bB, hDifferent⟩ := hTargetTwo
  have hTwo : ∀ r : {r : DesignatedCopy B D stage.system family //
      r ∈ stage.selected},
      ∃ e₁ e₂ : OldACarrierEdge A stage.system.toRelStructure,
        e₁ ≠ e₂ ∧ e₁.1 ⊆ copyCarrier r.1.embedding ∧
          e₂.1 ⊆ copyCarrier r.1.embedding := by
    intro r
    exact selectedCopy_two_edges_of_target
      A B D stage.system family stage.selected
      r aB bB hDifferent
  have hRel : ∀ (μ : Fin ((q :: tail).length + 1)) (i : I)
      (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
      stage.train.rel μ p.1 r.1 ↔
        U.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i p)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            S E.toRelStructure RF i r) := by
    apply sharedSupportTrainRel_of_interior stage.train U
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
        S E.toRelStructure RF)
    intro μ hZero hTop i p r
    exact hInterior μ (by omega) (by omega) i p r
  intro j hj
  exact attachedSelectedPicture_fullSystemGirth_of_projectedACopies
    A hA B D stage.system family stage.selected e E.toRelStructure RF
      stage.train U Shared hRel j.castSucc
    stage.projectsACopies hBaseLinear hRigid hStrong hTwo
    ((q :: tail).get j) (hCutoff j)
    (stage.tailGirth j hj) (by
      simpa only [activeGluingWitnessOrderOneData_eq_shared
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U j.castSucc]
        using hPositive j hj)

end PositiveFt
end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
