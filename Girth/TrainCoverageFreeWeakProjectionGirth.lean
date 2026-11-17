import Girth.TrainCoverageFreeACopyGeometry
import Girth.TrainActualOneLevelGirthIntrinsic
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# One-level selected FULL system-girth transfer from weak A-copy projection

The existing one-level "intrinsic geometry" theorem requests full
order-expanded IsPartiteOver only to derive that the true active
carrier is A-strong. That step works with ProjectsACopies instead.
All remaining inputs and conclusion are literally the old theorem's.

This is a local replacement of an overstrong geometric hypothesis,
not a new forest assertion or a rewrite of the recursive construction.
Source candidate: exact-head Lean kernel validation still required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section WeakOneLevelOutputGirth

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce
    (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I,
  Nonempty (SharedOldACarrierEdge A C.toRelStructure
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
local notation "CoreCar" =>
  attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Old" =>
  selectedPictureOrderOneData A B D C family selected T μ
local notation "Wit" =>
  sharedWitnessOrderOneData U μ Emb
    (Subtype.val : CoreEdge → Set Y)
local notation "Out" =>
  attachedSelectedPictureOrderOneData
    A hA B D C family selected e R f T U hShared μ

include hRel

/-- Genuine one-level original B-labelled system-girth preservation
from physical A-copy base projection. The old full order-expanded
IsPartiteOver hypothesis is unnecessary for this transfer. -/
theorem attachedSelectedPicture_fullSystemGirth_of_projectedACopies
    [Finite UA]
    (hProjected : ProjectsACopies A D C)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : Embedding A D, SameCopy b e → b = e)
    (hStrong : ∀ r : Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (q : ℕ) (hq : 2 ≤ q)
    (hOldFull : (Old).FullSystemGirthGT q)
    (hWitness : (Wit).FullSystemGirthGT q) :
    (Out).FullSystemGirthGT q := by
  have hActive : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_projectedACopies
      A D C hProjected hBaseLinear e hRigid
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

end WeakOneLevelOutputGirth
end StructuralRamsey.Girth
