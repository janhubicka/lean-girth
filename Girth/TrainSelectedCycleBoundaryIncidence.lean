import Girth.TrainSelectedPictureOutputIncidence
import Girth.TrainBigCyclePhysicalIncidence

/-!
# Circulation: labelled-cycle wagon incidences are actual old edges

A wagon connector in an actual selected-picture BigCycle has incident
physical A-support edges on both sides. If the adjacent occurrence
labels are inherited from prescribed standards, the verified
selected-picture edge-pullback theorem gives REAL old A-support
edges of the corresponding labels, with exactly the same output
wagon class.

This is the necessary typed input for standard/standard and
standard/core boundary contraction. It does not assume a reduct,
segment minimality, or output pretrain linearity. No appendix input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SelectedBoundary

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

local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f
    (physicalStandardEdge
      (sharedOldACarrierInclusion A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding))
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f) i a))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure (activeCarrier A C e.toFunctionEmbedding)
  R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

/-- At a REAL output big-cycle wagon boundary, standard-labelled
occurrences on both sides admit genuine old incident support edges,
and their images meet the very same physical output wagon. -/
theorem attachedSelectedPicture_cycle_wagon_boundary_source_edges
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i j : I) (a b : Label)
    (hW : K.connector k = Sum.inr W)
    (ha : K.label k = LabelMap i a)
    (hb : K.label (cyclicSucc k) = LabelMap j b) :
    ∃ oldA oldB : OldEdge,
      oldA ∈ (Old).edges a ∧
      oldB ∈ (Old).edges b ∧
      (Out).parent (StdEdge i oldA) = W ∧
      (Out).parent (StdEdge j oldB) = W := by
  obtain ⟨edgeA, edgeB, hEdgeA, hParentA, hEdgeB, hParentB⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hMeetsA : (Out).Meets (LabelMap i a) W :=
    ⟨edgeA, by simpa only [ha] using hEdgeA, hParentA⟩
  have hMeetsB : (Out).Meets (LabelMap j b) W :=
    ⟨edgeB, by simpa only [hb] using hEdgeB, hParentB⟩
  obtain ⟨oldA, hOldA, hWA⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ i a W).mp hMeetsA
  obtain ⟨oldB, hOldB, hWB⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ j b W).mp hMeetsB
  exact ⟨oldA, oldB, hOldA, hOldB, hWA, hWB⟩

end SelectedBoundary

end StructuralRamsey.Girth
