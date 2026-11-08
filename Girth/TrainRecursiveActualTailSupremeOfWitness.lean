import Girth.TrainActualTwoCycleWitnessDoubleWagonExclusion
import Girth.TrainRecursiveWitnessPass
import Girth.ActiveCarrierStrong
import Girth.TrainSelectedPictureStageGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# Track B: actual lower witness supplies ALL original positive tail supreme bounds

The nontrivial refining PictureStep requests output SupremeCycleBound
at every original positive old cut. This is NOT a fresh girth premise:
the old ForestTailStage already has complete positive selected-picture
FullSystemGirthGT; the genuine lower shared witness supplies full
system girth at the corresponding cuts. Under the explicit attachment
linearity and whole-copy strongness geometry, the Path A physical
original-source theorem gives the output FullSystemGirthGT at each
old positive cut, and hence its SupremeCycleBound projection.

All physical edges, selected B labels, wagon relations and original
cut indices are used without quotienting. The remaining job is to
derive the lower witness's complete positive certificates and all
attachment geometry from the actual selected lower induction.
The Path A theorem itself remains a draft pending exact-head CI.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
variable (B : RelStructure L VB) (D : RelStructure L P)
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestTailStage A B D family t targetTrain allowed)
variable (e : Embedding A D)
variable (R : RelStructure L Y)
variable (f : I → Embedding
  (S.system.toRelStructure.induce
    (activeCarrier A S.system e.toFunctionEmbedding)) R)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) t.length)
variable (hShared : ∀ _i : I,
  Nonempty (SharedOldACarrierEdge A S.system.toRelStructure
    (activeCarrier A S.system e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (t.length + 1)) (i : I)
  (p q : SharedOldACarrierEdge A S.system.toRelStructure
    (activeCarrier A S.system e.toFunctionEmbedding)),
  S.train.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) R f i p)
      (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
        (activeCarrier A S.system e.toFunctionEmbedding) R f i q))

local notation "Selected" =>
  {b : DesignatedCopy B D S.system family // b ∈ S.selected}
local notation "OldEdge" => OldACarrierEdge A S.system.toRelStructure
local notation "Out" => fun ν : Fin (t.length + 1) =>
  attachedSelectedPictureOrderOneData
    A hA B D S.system family S.selected e R f S.train U hShared ν
local notation "Wit" => fun ν : Fin (t.length + 1) =>
  sharedWitnessOrderOneData U ν
    (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) R f)
    (Subtype.val : OldACarrierEdge A R → Set Y)

include hRel

/-- The actual old selected ForestTailStage and genuine lower shared
FullSystemGirthGT imply ALL original positive attached-output
SupremeCycleBound certificates, provided the explicit physical
attachment hypotheses of the Path A theorem hold at those cuts.

This discharges the *hTail* proof field of the nontrivial Track B local
refinement, not the existence of the lower selected witness. -/
theorem ForestTailStage.attachedAllPositiveSupreme_of_actualWitness
    (hTwoCut : ∀ j : Fin t.length, 0 < j.val → 2 ≤ t.get j)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A S.system e.toFunctionEmbedding)
    (hStrong : ∀ r : Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hWitness : ∀ j : Fin t.length, 0 < j.val →
      (Wit j.castSucc).FullSystemGirthGT (t.get j)) :
    ∀ j : Fin t.length, 0 < j.val →
      (Out j.castSucc).SupremeCycleBound (t.get j) := by
  intro j hj
  have hOldStrong : AStrong A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) :=
    activeCarrier_aStrong_of_base_aLinear
      A D S.system hA S.isPartite hBaseLinear e hRigid
  have hTwoCopies : ∀ r : Selected, ∃ a d : OldEdge,
      a ≠ d ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        d.1 ⊆ copyCarrier r.1.embedding := by
    obtain ⟨a, b, hDistinct⟩ := hTargetTwo
    intro r
    refine ⟨actualEdge (r.1.embedding.comp a),
      actualEdge (r.1.embedding.comp b), ?_, ?_, ?_⟩
    · intro hab
      apply hDistinct
      apply sameCopy_of_comp r.1.embedding
      change copyCarrier (r.1.embedding.comp a) =
        copyCarrier (r.1.embedding.comp b)
      exact congrArg (fun edge : OldEdge => edge.1) hab
    · change copyCarrier (r.1.embedding.comp a) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    · change copyCarrier (r.1.embedding.comp b) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨b u, rfl⟩
  have hFullGluing :
      (activeGluingWitnessOrderOneData A S.system
        e.toFunctionEmbedding R f U j.castSucc).FullSystemGirthGT
          (t.get j) := by
    rw [activeGluingWitnessOrderOneData_eq_shared
      A S.system e.toFunctionEmbedding R f U j.castSucc]
    exact hWitness j hj
  have hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)) :=
    activeGluingWitness_images_aStrong_of_fullSystemGirth
      A S.system e.toFunctionEmbedding R f U j.castSucc
      (t.get j) (hTwoCut j hj) hFullGluing
  have hHeight : 2 ≤ t.length := by
    have hjLt := j.isLt
    omega
  have hCoreCut : ∀ μ : Fin (t.length + 1),
      0 < μ.val → μ.val < t.length →
      (activeGluingWitnessOrderOneData A S.system
        e.toFunctionEmbedding R f U μ).FullSystemGirthGT 2 := by
    intro μ hPos hLt
    let k : Fin t.length := ⟨μ.val, hLt⟩
    have hk : 0 < k.val := hPos
    have hq : 2 ≤ t.get k := hTwoCut k hk
    have hActual :
        (activeGluingWitnessOrderOneData A S.system
          e.toFunctionEmbedding R f U μ).FullSystemGirthGT (t.get k) := by
      rw [activeGluingWitnessOrderOneData_eq_shared
        A S.system e.toFunctionEmbedding R f U μ]
      have hCast : k.castSucc = μ := Fin.ext rfl
      simpa only [← hCast] using hWitness k hk
    refine ⟨hActual.1, ?_⟩
    intro n K hAccept hOrder
    exact hActual.2 n K hAccept (by omega)
  have hGeometry :=
    S.activeAttachment_allLevels_linear_and_strong_of_two_le_height
      hA hBaseLinear e hRigid active R f U hHeight
      (fun μ _ _ i p q => hRel μ i p q)
      (fun _ => 2) (fun _ _ _ => Nat.le_refl 2) hCoreCut
  have hLinear : (Out j.castSucc).LinearPretrain := by
    exact (hGeometry.2 j.castSucc).1
  have hOld : (selectedPictureOrderOneData A B D S.system family
      S.selected S.train j.castSucc).SupremeCycleBound (t.get j) :=
    (S.tailGirth j hj).2
  have hOut : (Out j.castSucc).FullSystemGirthGT (t.get j) :=
    attachedSelectedPicture_fullSystemGirth_of_actual_witness
      A hA B D S.system family S.selected e R f S.train U
      hShared hRel j.castSucc
      (t.get j) (Nat.le_trans (by decide : 1 ≤ 2) (hTwoCut j hj))
      hLinear hStrong
      hTwoCopies hOldStrong hCoreStrong hOld (hWitness j hj)
  exact hOut.2

end StructuralRamsey.Girth.TrainRecursiveWitness
