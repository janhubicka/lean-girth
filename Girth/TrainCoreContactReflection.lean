import Girth.TrainCoreWagonEmbedding
import Girth.TrainSelectedPictureOutputIncidence
import Girth.TrainActualPhysicalEdgeCarrierEval

/-!
# Genuine witness-core contacts and pair edges reflect to the attached picture

For the actual core witness we use the EDGE CARRIERS IN THE CORE, not
their output images: its vertices are Y and its edges are genuine
OldACarrierEdge A R. The vertex embedding is the actual attachment
coreEmbedding, and the wagon map is the injective class transport.

Every vertex contact with EVERY core wagon transfers to the embedded
output wagon, since the core wagon is a class of genuine support edges.
Every ambient pair-edge of the core likewise transfers as a genuine
physical A-support edge of the attachment. These are exactly the
all-wagon and pair-reflection inputs of the cyclic restriction map.

No segmentation or chosen cut connectors are assumed, and the result
does not claim A1--A3 transfer without those remaining inputs.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section CoreContactReflection

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
variable (hPreserve : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 →
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (fun b : CoreEdge => b.1)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U hPreserve hShared μ

/-- Any two actual core vertices joined by an actual core support edge
remain joined by its canonical physical output A-support edge. No
linear/girth bound or assumption on a selected cycle is needed. -/
theorem attachedSelectedPicture_core_pairEdge_reflect
    (x y : Y) (hPair : (Wit).PairEdge x y) :
    (Out).PairEdge (CoreEmb x) (CoreEmb y) := by
  obtain ⟨b, hx, hy⟩ := hPair
  refine ⟨CoreActual b, ?_, ?_⟩
  · change CoreEmb x ∈ (CoreActual b).1
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f b]
    exact ⟨x, hx, rfl⟩
  · change CoreEmb y ∈ (CoreActual b).1
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f b]
    exact ⟨y, hy, rfl⟩

/-- The source contact condition is true for EVERY core wagon, not
only the wagons used as cyclic connectors. Its actual edge witness
maps to the same generated output wagon under the injective κ map. -/
theorem attachedSelectedPicture_core_wagonContact_reflect
    (p : Quotient (U.wagonSetoid μ)) (x : Y)
    (hContact : (Wit).WagonVertex p x) :
    (Out).WagonVertex (CoreWagon p) (CoreEmb x) := by
  obtain ⟨b, hb, hx⟩ := hContact
  refine ⟨CoreActual b, ?_, ?_⟩
  · change Quotient.mk ((Train).wagonSetoid μ) (CoreActual b) =
      CoreWagon p
    calc
      Quotient.mk ((Train).wagonSetoid μ) (CoreActual b) =
        CoreWagon (Quotient.mk (U.wagonSetoid μ) b) :=
          (generatedActualASupportTrain_coreWagonEmbedding_mk
            A hA C.toRelStructure S R f T U hPreserve hShared μ b).symm
      _ = CoreWagon p := by
        exact congrArg CoreWagon hb
  · change CoreEmb x ∈ (CoreActual b).1
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f b]
    exact ⟨x, hx, rfl⟩

end CoreContactReflection
end StructuralRamsey.Girth
