import Girth.TrainSelectedCycleBoundaryIncidence
import Girth.TrainActualStandardCoreIncidence

/-!
# Circulation: actual standard/core wagon boundary of a selected big cycle

A physical wagon connector between a prescribed standard occurrence
and a singleton genuine witness A-edge has genuine source incidences.
The standard source edge is pulled back through the actual selected
label map, and the core edge is literally the singleton label.
The checked physical contact lemma therefore supplies a shared old
A-edge whose core image lies in the SAME witness wagon and inside Q_i.

The conclusion is copy-local and does not assume the reduct is legal.
The shared-support hRel/hShared inputs remain explicit.
No appendix theorem is imported.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section SelectedCoreWagonBoundary

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
variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
      Emb i a))
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

include hRel

/-- Real standard/core wagon boundary of an actual selected BigCycle.
Its standard label supplies an old physical edge and a genuinely
shared local bridge whose core image belongs to Q_i and the wagon
of the specified singleton core edge. -/
theorem attachedSelectedPicture_cycle_wagon_standard_core_copy_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i : I) (a : Label) (b : CoreEdge)
    (hW : K.connector k = Sum.inr W)
    (ha : K.label k = LabelMap i a)
    (hb : K.label (cyclicSucc k) = Sum.inr (CoreActual b)) :
    ∃ (old : OldEdge) (s : SharedOldACarrierEdge A C.toRelStructure S),
      old ∈ (Old).edges a ∧
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
      U.rel μ (Emb i s) b ∧
      (Emb i s).1 ⊆ Set.range (f i) := by
  obtain ⟨edgeA, edgeB, hEdgeA, hParentA, hEdgeB, hParentB⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hMeetsA : (Out).Meets (LabelMap i a) W :=
    ⟨edgeA, by simpa only [ha] using hEdgeA, hParentA⟩
  obtain ⟨old, hOld, hWOld⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ i a W).mp hMeetsA
  have hCoreEq : edgeB = CoreActual b := by
    rw [hb] at hEdgeB
    change edgeB = CoreActual b at hEdgeB
    exact hEdgeB
  have hWCore : (Out).parent (CoreActual b) = W := by
    simpa only [hCoreEq] using hParentB
  have hSame : (Train).rel μ (StdEdge i old) (CoreActual b) :=
    Quotient.exact (hWOld.trans hWCore.symm)
  obtain ⟨s, hsOld, hsCore, hsLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i old b hSame
  exact ⟨old, s, hOld, hsOld, hsCore, hsLocal⟩


/-- Reverse physical orientation: the same wagon supports a singleton
core edge on the left and an indexed standard on the right. The old
standard edge and shared core bridge belong to the SPECIFIED local
copy; hShared and hRel remain explicit. -/
theorem attachedSelectedPicture_cycle_wagon_core_standard_copy_local
    {n : ℕ} (K : (Out).BigCycle n)
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i : I) (a : Label) (b : CoreEdge)
    (hW : K.connector k = Sum.inr W)
    (hb : K.label k = Sum.inr (CoreActual b))
    (ha : K.label (cyclicSucc k) = LabelMap i a) :
    ∃ (old : OldEdge) (s : SharedOldACarrierEdge A C.toRelStructure S),
      old ∈ (Old).edges a ∧
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
      U.rel μ (Emb i s) b ∧
      (Emb i s).1 ⊆ Set.range (f i) := by
  obtain ⟨edgeB, edgeA, hEdgeB, hParentB, hEdgeA, hParentA⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hMeetsA : (Out).Meets (LabelMap i a) W :=
    ⟨edgeA, by simpa only [ha] using hEdgeA, hParentA⟩
  obtain ⟨old, hOld, hWOld⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ i a W).mp hMeetsA
  have hCoreEq : edgeB = CoreActual b := by
    rw [hb] at hEdgeB
    change edgeB = CoreActual b at hEdgeB
    exact hEdgeB
  have hWCore : (Out).parent (CoreActual b) = W := by
    simpa only [hCoreEq] using hParentB
  have hSame : (Train).rel μ (StdEdge i old) (CoreActual b) :=
    Quotient.exact (hWOld.trans hWCore.symm)
  obtain ⟨s, hsOld, hsCore, hsLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i old b hSame
  exact ⟨old, s, hOld, hsOld, hsCore, hsLocal⟩

end SelectedCoreWagonBoundary

end StructuralRamsey.Girth
