import Girth.TrainCoverageFreeForestOrderStep
import Girth.TrainCoverageFreeBoundsFromMixed
import Girth.TrainCoverageFreePositiveTransfer
import Girth.TrainRecursiveNontrivialFibre
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# SAME-VECTOR F_t -> selected coverage-free OrderStage on a real fibre

The genuine standalone F_t witness supplies mixed finite SET
forests, full positive system bounds, complete selected support
images, partite train embeddings and a physical A-edge Ramsey
arrow. It does NOT supply recursive selected mixedCoverage.

For a nontrivial actual projected fibre with two distinct
physical A-copy carriers, this theorem combines:
- the SAME-q mixed F_t forest (not a fictitious bottom local
  system-girth assertion);
- the actual physical local core A-support (nonempty and
  covering all core vertices), not total A-irreducible extension;
- the correct universal TOP cutoff-two bound when q=2;
- exact shared wagon-train compatibility and adjacent parameters;
- old selected base A-strongness and selected base lifts;
- the checked exact positive proper-cut output transfer.

The resulting next coverage-free OrderStage has full original
B-labelled system girth at ALL requested cutoffs, including
bottom q, and an actual selected Ramsey PictureStep for the
processed profile. No extra local mixed irred-coverage or
stronger embedding-colouring Ramsey arrow is assumed.

The theorem is still conditional on the actual selected F_t
witness (partite core, exact train, parameters and physical
Ramsey arrow) and on the old-stage geometry. The full finite
pass is a separate, already coverage-free, combinatorial theorem.
No Lean kernel compilation has yet been run.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section RealMixedFtNontrivial

variable (stage : ForestStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels
  (OldACarrierEdge A E.toRelStructure) (q :: tail).length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Bottom" =>
  (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))
local notation "Old" => (fun μ : Fin ((q :: tail).length + 1) =>
  selectedPictureOrderOneData A B D stage.system
    family stage.selected stage.train μ)
local notation "Out" => (fun μ : Fin ((q :: tail).length + 1) =>
  attachedSelectedPictureOrderOneData A hA B D stage.system
    family stage.selected e E.toRelStructure RF
    stage.train U Shared μ)

variable (hBaseCovered : stage.CoversBase)
variable (hSelectedStrong :
  ∀ b : DesignatedCopy B D stage.system family,
    b ∈ stage.selected → AStrong A D (copyCarrier b.base))
variable (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
variable (hCutoff : ∀ j : Fin (q :: tail).length,
  2 ≤ (q :: tail).get j)
variable (hInterior : ∀ μ : Fin ((q :: tail).length + 1),
  0 < μ.val → μ.val < (q :: tail).length →
  ∀ (i : I) (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
    stage.train.rel μ p.1 r.1 ↔
      U.rel μ
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF i p)
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          S E.toRelStructure RF i r))
variable (hPositive : ∀ j : Fin (q :: tail).length, 0 < j.val →
  (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding
    E.toRelStructure RF U j.castSucc).FullSystemGirthGT
      ((q :: tail).get j))

/-- One selected local F_t witness with the actual MIXED core
triple constructs the entire mixed attachment bounds and a
next ORDER-stage selected PictureStep at the SAME cutoff q::tail.
No hCoreCoverage oracle, output-girth oracle, independent q-1
forest or top-cutoff-two oracle. -/
theorem ForestStage.orderPictureStep_of_nontrivial_Ft
    (hReady : stage.BottomReady)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hCorePartite : E.IsPartiteOver D)
    (hCoreSupportNonempty :
      Nonempty (OldACarrierEdge A E.toRelStructure))
    (hCoreSupportCovers : ∀ y : Y,
      ∃ edge : OldACarrierEdge A E.toRelStructure,
        y ∈ edge.1)
    (hSelectedSupports : Function.Injective
      (fun i : I => bSupportPiece A (RF i)))
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q)
    (hCoreParameters : U.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => E.part ⁻¹' allowed ν))
    (κ : Type w) [Nonempty κ]
    (hCarrierRigid : ∀ a b : Embedding A E.toRelStructure,
      SameCopy a b → a = b)
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
        ∃ i : I,
          ∀ a b : Embedding A (stage.system.induce S).toRelStructure,
            χ (actualEdge ((RF i).comp a)) =
              χ (actualEdge ((RF i).comp b))) :
    ∃ next : OrderStage A B D family (q :: tail)
      targetTrain allowed,
      PictureStep stage next.toForestStage
        e.toFunctionEmbedding κ := by
  obtain ⟨pa, pb, hDifferent⟩ := hPair
  obtain ⟨edge₁, edge₂, hEdgeNe⟩ :=
    activeSupport_two_distinct_of_projected_carriers
      A stage.system e.toFunctionEmbedding pa pb hDifferent
  obtain ⟨a, ha⟩ := edge₁.2
  obtain ⟨b, hb⟩ := edge₂.2
  have hSourceTwo : ¬ SameCopy a b := by
    intro hSame
    apply hEdgeNe
    apply Subtype.ext
    exact ha.trans (hSame.trans hb.symm)
  have hOutputPositive :=
    stage.actual_positive_full_of_Ft
      hA hBaseLinear e hRigid active E f U
      hBaseCovered hSelectedStrong hTargetTwo hCutoff
      hInterior hPositive
  have hInteriorTwo :
      ∀ μ : Fin ((q :: tail).length + 1),
        0 < μ.val → μ.val < (q :: tail).length →
        (activeGluingWitnessOrderOneData A stage.system
          e.toFunctionEmbedding E.toRelStructure RF U μ)
          .FullSystemGirthGT 2 := by
    intro μ hPos hLt
    let j : Fin (q :: tail).length := ⟨μ.val, hLt⟩
    have hμ : j.castSucc = μ := Fin.ext rfl
    rw [← hμ]
    obtain ⟨hLinear, hSupreme⟩ := hPositive j hPos
    refine ⟨hLinear, ?_⟩
    intro n Z hAccept hOrder
    exact hSupreme n Z hAccept
      (by have hCut := hCutoff j; omega)
  have hTailSupreme :
      ∀ j : Fin (q :: tail).length, 0 < j.val →
        (Out j.castSucc).SupremeCycleBound ((q :: tail).get j) := by
    intro j hj
    exact (hOutputPositive j hj).2
  have hHead : 2 ≤ (q :: tail).headD 0 := by
    simpa using hCutoff
      (⟨0, by simp⟩ : Fin (q :: tail).length)
  have hSource : 2 < (q :: tail).headD 0 →
      ∃ e₀ e₁ : Set S,
        e₀ ∈ supportCopies A
          (stage.system.induce S).toRelStructure ∧
        e₁ ∈ supportCopies A
          (stage.system.induce S).toRelStructure ∧
        e₀ ≠ e₁ := by
    intro _hGt
    exact ⟨edge₁.1, edge₂.1, edge₁.2, edge₂.2,
      fun hEq => hEdgeNe (Subtype.ext hEq)⟩
  have hBounds : ActiveAttachmentBounds
      stage hA e active E f U :=
    ActiveAttachmentBounds.of_sameVector_finiteMixed
      stage hA e active E f U
      hCorePartite hCoreSupportNonempty hCoreSupportCovers hSelectedStrong hTargetTwo
      hInterior hHead hSource hSelectedSupports hForest
      hCoreParameters hInteriorTwo hTailSupreme
  exact stage.activeAttachment_orderPictureStep_of_physicalFt
    hA hBaseLinear e hRigid active E f U hBounds
    hReady hBaseCovered a b hSourceTwo
    hSelectedSupports hForest κ hCarrierRigid hPhysicalArrow

end RealMixedFtNontrivial

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
