import Girth.TrainActualStandardWagonMap
import Girth.TrainActualCoreRestrictionMap

/-!
# Actual standard embedding supplies cyclic restriction geometry

Every old A-support edge of one standard embeds as an actual physical
output A-edge with exactly its carrier. The exact standard wagon
relation gives an injective old-to-output wagon quotient map. Hence
old pair edges and contacts with every old wagon reflect to the
attached output. These are the two semantic fields of the cyclic
restriction map.

Given a legal old BigCycle with the correct connector word, the
complete standard restriction map is automatic. Old-cycle existence
and its faithful labels are separate. No appendix result is used.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section StandardRestrictionGeometry

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
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "StdEdge" => fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge
      (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i a)
local notation "Train" =>
  generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Old ambient pair edges map to genuine output support edges. -/
theorem attachedSelectedPicture_standard_pairEdge_reflect
    (i : I) (x y : X) (hPair : (Old).PairEdge x y) :
    (Out).PairEdge (Std i x) (Std i y) := by
  obtain ⟨old, hx, hy⟩ := hPair
  refine ⟨StdEdge i old, ?_, ?_⟩
  · change Std i x ∈ (StdEdge i old).1
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i old]
    exact ⟨x, hx, rfl⟩
  · change Std i y ∈ (StdEdge i old).1
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i old]
    exact ⟨y, hy, rfl⟩

/-- Contacts with ALL old standard wagons reflect to the actual
output wagon determined by the injective standard quotient map. -/
theorem attachedSelectedPicture_standard_wagonContact_reflect
    (i : I) (p : Quotient (T.wagonSetoid μ)) (x : X)
    (hContact : (Old).WagonVertex p x) :
    (Out).WagonVertex (StdWagon i p) (Std i x) := by
  obtain ⟨old, hOldParent, hx⟩ := hContact
  refine ⟨StdEdge i old, ?_, ?_⟩
  · change Quotient.mk ((Train).wagonSetoid μ) (StdEdge i old) =
      StdWagon i p
    calc
      Quotient.mk ((Train).wagonSetoid μ) (StdEdge i old) =
        StdWagon i (Quotient.mk (T.wagonSetoid μ) old) :=
          (generatedActualASupportTrain_standardWagonEmbedding_mk
            A hA C.toRelStructure S R f T U hRel hShared μ i old).symm
      _ = StdWagon i p := congrArg (StdWagon i) hOldParent
  · change Std i x ∈ (StdEdge i old).1
    rw [actualAPictureEdgeEquiv_standard_carrier
      A hA C.toRelStructure S R f i old]
    exact ⟨x, hx, rfl⟩

/-- The standard embeddings supply the complete physical cyclic
restriction geometry from any legal old BigCycle with the correct
connector image. No extra contacts or pair-reflection assumptions. -/
noncomputable def attachedSelectedPicture_standard_restrictionMap
    (i : I) {n : ℕ} (K : (Out).BigCycle n)
    (Z : (Old).BigCycle n)
    (hConnector : ∀ k : Fin n,
      K.connector k =
        Sum.map (Std i) (StdWagon i) (Z.connector k)) :
    K.RestrictionMap Z := by
  refine {
    position := {
      toFun := fun j => j
      inj' := by intro a b h; exact h
      map_rel_iff' := by intro a b; rfl
    }
    vertex := Std i
    wagon := StdWagon i
    vertex_injective := (Std i).injective
    wagon_injective := (StdWagon i).injective
    connector_eq := hConnector
    contact := ?_
    pair_reflect := ?_
  }
  · intro p j x _ hContact
    exact attachedSelectedPicture_standard_wagonContact_reflect
      A hA B D C family selected e R f T U hShared hRel μ
      i p x hContact
  · intro j p x y _ _ _ _ _ _ hPair
    exact attachedSelectedPicture_standard_pairEdge_reflect
      A hA B D C family selected e R f T U hShared hRel μ
      i x y hPair

end StandardRestrictionGeometry
end StructuralRamsey.Girth
