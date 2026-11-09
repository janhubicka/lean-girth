import Girth.TrainActualTwoCycleWitnessDoubleWagonExclusion
import Girth.TrainSelectedPictureIntrinsicGeometry
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Track A: one-level output system girth from intrinsic picture-step geometry

The preceding full original n=2 / n>=3 two-cut theorem takes the
literal output LinearPretrain and A-strongness of the active fibre and
complete core gluing images as explicit hypotheses.

At cutoff q>=2 those geometric hypotheses are consequences of the
actual inputs used in the circulation's picture pass:
* an A-partite old picture over an A-linear base and the processed
  base copy's rigidity make the true active fibre A-strong;
* genuine lower-witness FullSystemGirthGT q makes every complete
  gluing image A-strong, via the actual active-witness = shared-witness
  identity and the checked pair-edge local-order-two probe;
* the lower-witness vertex-image girth and old picture linearity give
  literal output LinearPretrain for the generated wagon partition.

The old full system bound supplies the old supreme-cycle bound.
This theorem performs only that checked composition and invokes the
actual attached-output theorem. It is still a ONE-LEVEL result,
conditional on the exact gluing-train relation and two old support
edges in each selected target copy. It does NOT construct the
recursive lower witness, prove the full partite lemma, or claim
an unverified manuscript validation marker.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section IntrinsicOneLevelOutputGirth

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Emb" =>
  sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreCar" =>
  attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Old" =>
  selectedPictureOrderOneData A B D C family selected T μ
local notation "Wit" =>
  sharedWitnessOrderOneData U μ Emb (Subtype.val : CoreEdge → Set Y)
local notation "Out" =>
  attachedSelectedPictureOrderOneData
    A hA B D C family selected e R f T U hShared μ

include hRel

/-- Under the circulation's intrinsic A-partite/linear/rigid geometry,
old and lower-witness FULL system girth at cutoff >=2 imply actual
one-level attached selected-output full system girth. No independent
output linearity or core-image strongness assumptions remain. -/
theorem attachedSelectedPicture_fullSystemGirth_of_intrinsic_geometry
    [Finite UA]
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (q : ℕ) (hq : 2 ≤ q)
    (hOldFull : (Old).FullSystemGirthGT q)
    (hWitness : (Wit).FullSystemGirthGT q) :
    (Out).FullSystemGirthGT q := by
  have hActive : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid
  have hActiveWitness :
      (activeGluingWitnessOrderOneData
        A C e.toFunctionEmbedding R f U μ).FullSystemGirthGT q := by
    rw [activeGluingWitnessOrderOneData_eq_shared
      A C e.toFunctionEmbedding R f U μ]
    exact hWitness
  have hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)) :=
    activeGluingWitness_images_aStrong_of_fullSystemGirth
      A C e.toFunctionEmbedding R f U μ q hq hActiveWitness
  let core := RelStructure.Attachment.coreEmbedding
    C.toRelStructure S R f
  have hCoreImage :
      (sharedWitnessOrderOneData U μ Emb CoreCar).FullSystemGirthGT q :=
    sharedWitnessOrderOneData_fullSystemGirth_vertexImage
      U μ Emb (fun edge : CoreEdge => edge.1)
      core.toFunctionEmbedding hWitness
  have hLocal :
      (sharedWitnessOrderOneData U μ Emb CoreCar).LocalPieceSystemBound 2 := by
    intro n Z hAccept hOrder
    exact (sharedWitnessOrderOneData U μ Emb CoreCar).localPieceSystemBound_of_supremeCycleBound
      q hCoreImage.2 n Z hAccept
      (hOrder.trans (Nat.mul_le_mul_left 2 hq))
  have hOutputLinear : (Out).LinearPretrain :=
    (attachedSelectedPicture_linear_and_strong_of_gluing_geometry
      A hA B D C family selected e R f T U hShared μ hRel
      hOldFull.1 hCoreImage.1 hLocal hActive hCoreStrong).1
  exact attachedSelectedPicture_fullSystemGirth_of_actual_witness
    A hA B D C family selected e R f T U hShared hRel μ
    q (by omega) hOutputLinear hStrong hTwoCopies
    hActive hCoreStrong hOldFull.2 hWitness

end IntrinsicOneLevelOutputGirth
end StructuralRamsey.Girth
