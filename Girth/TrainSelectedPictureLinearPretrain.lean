import Girth.TrainSelectedPictureEdgeLinearity
import Girth.TrainSelectedPictureWagonLinearity

set_option Elab.async false

/-!
# Linear and strong generated output geometry

Combine the independently verified physical edge and complete wagon-carrier
intersection theorems into the existing full LinearPretrain predicate. The
whole attached-standard formulation needs no additional core-image assumption.
A second interface supplies standard strongness from the usual complete
core gluing-image geometry and packages both output conclusions.

Neither endpoint assumes output system-girth or global replacement legality.
Recursive discharge of the source geometry and cycle transfer remain separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section LinearPretrain

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
variable (μ : Fin (m + 1))
variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k q))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  Eqv (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel


/-- Full linearity of the actual generated pretrain: both physical support
edges and complete generated wagon carriers have subsingleton intersections.
All linearity and strongness inputs belong to the source geometry. -/
theorem attachedSelectedPicture_linearPretrain
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i))) :
    (Out).LinearPretrain := by
  constructor
  · exact attachedSelectedPicture_edge_carriers_inter_subsingleton
      A hA B D C family selected e R f T U μ hOld hCore hActive hStd
  · exact attachedSelectedPicture_wagon_vertices_inter_subsingleton
      A hA B D C family selected e R f T U hShared μ hRel
      hOld hCore hBound hActive hStd

/-- The usual whole-gluing-image hypotheses supply the whole-standard
strongness input. Together the checked geometry yields a linear generated
pretrain and strongness of every complete generated wagon. This does not
assert the recursive construction supplies these geometric hypotheses. -/
theorem attachedSelectedPicture_linear_and_strong_of_gluing_geometry
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hBound : (Witness).LocalPieceSystemBound 2)
    (hActive : AStrong A C.toRelStructure S)
    (hImage : ∀ i : I, AStrong A R (copyCarrier (f i))) :
    (Out).LinearPretrain ∧
      ∀ W : Quotient ((Train).wagonSetoid μ),
        AStrong A Actual ((Train).wagonClassCarrier (fun a : ActualEdge => a.1) μ W) := by
  have hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)) :=
    fun i => attachment_copy_aStrong C.toRelStructure S R f hA hActive hImage i
  exact ⟨attachedSelectedPicture_linearPretrain
      A hA B D C family selected e R f T U hShared μ hRel
      hOld hCore hBound hActive hStd,
    attachedSelectedPicture_wagon_aStrong
      A hA B D C family selected e R f T U hShared μ hRel
      hOld hCore hBound hActive hStd⟩

end LinearPretrain

end StructuralRamsey.Girth
