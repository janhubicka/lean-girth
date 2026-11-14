import Girth.TrainActualAttachmentBoundsFromFiniteMixed
import Girth.TrainActualForestAttachmentPhysicalArrow
import Girth.TrainActualSelectedBaseCoverage
import Girth.TrainRecursiveNontrivialFibre
import Girth.TrainActualOneLevelGirthIntrinsic
import Girth.TrainSharedSupportInteriorCompatibility
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# One nontrivial F_t local witness gives the actual selected order picture step

This module removes the redundant local tailSupreme, cutoffTwo and
smaller forest/girth oracles from the earlier actual forest picture
attachment wrapper. The only supplied LOCAL F_t inputs are:
- a finite partite local train witness with A-irreducible coverage;
- the genuine finite-set mixed forest through the current SAME q;
- one selected image per physical support and the PHYSICAL A-edge arrow;
- positive proper local system-girth at the exact entries of tail;
- exact local adjacent parameters and shared-subsystem reflection.

The genuine OLD stage provides its own positive bound at each cut,
and its selected base projections are A-strong. Selected base coverage
gives the strongness for every prescribed base B-member required by
the checked older source transfer. Nontriviality of the true physical
projected fibre gives two distinct A-support edges in the honest
active induced target, so the q>2 local forest premise is derived.

Use the SAME positive local system bounds to obtain the actual
positive output supremeness demanded by ActiveAttachmentBounds.
At q=2 the universal-top theorem supplies the extra FullSystemGirthGT
2 witness. At the bottom the local F_t mixed forest produces output
FullSystemGirthGT q. No lower-rank recursive witness or output-girth
oracle is postulated.

The remaining global obligation is that F_t supplies these concrete
partite local inputs for EVERY ordered profile and that its arrows
can be chosen compatibly with the finite refinability Ready invariant.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

section ActualFibre

variable (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
variable (hA : A.Irreducible) [Finite UA] [Nontrivial UA]
variable (hBaseLinear : ALinear A D) (e : Embedding A D)
variable (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) (q :: tail).length)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "Bottom" =>
  (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A stage.system e.toFunctionEmbedding active I
local notation "Old" => (fun μ : Fin ((q :: tail).length + 1) =>
  selectedPictureOrderOneData A B D stage.system family stage.selected stage.train μ)
local notation "Out" => (fun μ : Fin ((q :: tail).length + 1) =>
  attachedSelectedPictureOrderOneData
    A hA B D stage.system family stage.selected e E.toRelStructure RF
    stage.train U Shared μ)
local notation "Wit" => (fun μ : Fin ((q :: tail).length + 1) =>
  sharedWitnessOrderOneData U μ
    (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
      S E.toRelStructure RF)
    (Subtype.val : OldACarrierEdge A E.toRelStructure → Set Y))

/-- The positive system bounds of the original stage and the true
positive local F_t witness give actual positive OUTPUT full
system-girth. There is no separate positive tailSupreme oracle. -/
theorem ForestTailStage.actual_positive_full_of_Ft
    (hBaseCovered : stage.CoversBase)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
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
    stage.allBaseStrong_of_selected hBaseCovered hSelectedStrong
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
  exact attachedSelectedPicture_fullSystemGirth_of_intrinsic_geometry
    A hA B D stage.system family stage.selected e E.toRelStructure RF
      stage.train U Shared hRel j.castSucc
    stage.isPartite hBaseLinear hRigid hStrong hTwo
    ((q :: tail).get j) (by have hCut:=stage.tailGirth j hj; omega)
    (stage.tailGirth j hj) (hPositive j hj)

/-- All actual ActiveAttachmentBounds and the next selected
OrderStage PictureStep follow from raw SAME-VECTOR F_t fields,
rather than a separately assumed tailSupreme/cutoffTwo certificate.
This theorem is for the genuine NONTRIVIAL active profile only. -/
theorem ForestTailStage.orderPictureStep_of_nontrivial_Ft
    (hReady : stage.BottomReady ∧ stage.CoversBase)
    (hSelectedStrong :
      ∀ b : DesignatedCopy B D stage.system family,
        b ∈ stage.selected → AStrong A D (copyCarrier b.base))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hProjectedPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hCorePartite : E.IsPartiteOver D)
    (hCoreCoverage : RelStructure.IrreduciblesExtendTo A E.toRelStructure)
    (hInterior : ∀ μ : Fin ((q :: tail).length + 1),
      0 < μ.val → μ.val < (q :: tail).length →
      ∀ (i : I) (p r : SharedOldACarrierEdge A stage.system.toRelStructure S),
        stage.train.rel μ p.1 r.1 ↔
          U.rel μ
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S E.toRelStructure RF i p)
            (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
              S E.toRelStructure RF i r))
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) q)
    (hCoreParameters : U.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => E.part ⁻¹' allowed ν))
    (hPositive : ∀ j : Fin (q :: tail).length, 0 < j.val →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U
        j.castSucc).FullSystemGirthGT ((q :: tail).get j))
    (κ : Type w) [Nonempty κ]
    (hCarrierRigid : ∀ a b : Embedding A E.toRelStructure,
      SameCopy a b → a = b)
    (hPhysicalArrow :
      ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
        ∃ i : I, ∀ a b : Embedding A (stage.system.induce S).toRelStructure,
          χ (actualEdge ((RF i).comp a)) =
            χ (actualEdge ((RF i).comp b))) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      PictureStep stage R.toForestTailStage e.toFunctionEmbedding κ := by
  obtain ⟨pa, pb, hDistinct⟩ := hProjectedPair
  obtain ⟨s, t, hst⟩ :=
    activeSupport_two_distinct_of_projected_carriers
      A stage.system e.toFunctionEmbedding pa pb hDistinct
  have hTwoSource :
      ∃ a b : Embedding A (stage.system.toRelStructure.induce S),
        ¬ SameCopy a b := by
    obtain ⟨a, ha⟩ := s.2
    obtain ⟨b, hb⟩ := t.2
    refine ⟨a, b, ?_⟩
    intro hEq
    apply hst
    apply Subtype.ext
    change copyCarrier a = copyCarrier b at hEq
    exact ha.trans (hEq.trans hb.symm)
  obtain ⟨a, b, hab⟩ := hTwoSource
  have hOutPositive :=
    stage.actual_positive_full_of_Ft
      hA hBaseLinear e hRigid active E f U
      hReady.2 hSelectedStrong hTargetTwo hInterior hPositive
  have hInteriorTwo : ∀ μ : Fin ((q :: tail).length + 1),
      0 < μ.val → μ.val < (q :: tail).length →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding E.toRelStructure RF U μ)
        .FullSystemGirthGT 2 := by
    intro μ hPos hLt
    let j : Fin (q :: tail).length := ⟨μ.val, hLt⟩
    have hj : 0 < j.val := hPos
    have hμ : j.castSucc = μ := Fin.ext rfl
    rw [← hμ]
    obtain ⟨hLin, hSup⟩ := hPositive j hj
    refine ⟨hLin, ?_⟩
    intro n C hAccept hOrder
    exact hSup n C hAccept (by omega)
  have hTailSupreme : ∀ j : Fin (q :: tail).length, 0 < j.val →
      (Out j.castSucc).SupremeCycleBound ((q :: tail).get j) := by
    intro j hj
    exact (hOutPositive j hj).2
  have hLocalTwo : 2 ≤ (q :: tail).headD 0 :=
    by simpa using
      (show 2 ≤ q from by
        have hRead := hReady.1
        have hF := stage.tailGirth
        omega)
  have hBounds : ActiveAttachmentBounds stage hA e active E f U :=
    ActiveAttachmentBounds.of_sameVector_finiteMixed
      stage hA e active E f U
      hCorePartite hCoreCoverage hSelectedStrong hTargetTwo
      hInterior hLocalTwo
      (fun hGt => by
        obtain ⟨e₁, e₂, hne⟩ :=
          activeSupport_two_distinct_of_projected_carriers
            A stage.system e.toFunctionEmbedding pa pb hDistinct
        exact ⟨e₁.1, e₂.1, e₁.2, e₂.2, fun h => hne (Subtype.ext h)⟩)
      hSelectedImages hForest hCoreParameters hInteriorTwo
      hTailSupreme
  have hOldBottom :
      (Old Bottom).FullSystemGirthGT q := hReady.1
  exact stage.activeAttachment_orderPictureStep_of_finiteMixed_physicalArrow
    hA hBaseLinear e hRigid active E f U hBounds
    hOldBottom hReady.2 a b hab
    hSelectedImages hForest κ hCarrierRigid hPhysicalArrow

end ActualFibre
end StructuralRamsey.Girth.TrainRecursiveWitness
