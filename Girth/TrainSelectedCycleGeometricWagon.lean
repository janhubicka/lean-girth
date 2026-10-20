import Girth.TrainSelectedCycleGeometricOwners
import Girth.TrainSelectedCycleStandardCoreWagon
import Girth.TrainActualCopyLocalCoreIncidence
import Girth.TrainActualStandardCoreIncidence

/-!
# Circulation: actual wagon boundaries of GEOMETRIC segment owners

A minimum geometric segmentation can place an occurrence from a foreign
designated label into a containing standard. Literal source-label
decomposition does not identify the chosen segment owner, and
rewriting its designated label could invalidate a prospective reduct.

A wagon boundary has a PHYSICAL support-edge incidence on either
side. Every actual output label's incident physical support edge lies
in that label's carrier. When the entire carrier belongs to a
geometrically chosen standard, the real edge pulls back to one old
A-support edge of that standard, with the SAME output wagon class.
No preservation of the original designated label is asserted.

This turns the checked actual generated-quotient incidence theorems
into wagon-boundary witnesses for all four geometric owner cases:
different standards, standard/core, core/standard, and core/core.
The first three still assume genuine shared-train compatibility hRel
and nonempty shared support hShared. These are precisely the
geometric input needed to CONSTRUCT the witness cycle, but do not
themselves establish cyclic segmentation, legal reduct or A1--A3.
No appendix theorem is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section GeometricSelectedCycleWagon

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
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (old : OldEdge) =>
  Eqv (physicalStandardEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) Emb i old))
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Every PHYSICAL edge supporting an output label lies in its
full physical carrier, both for prescribed copies and actual edges.
This simple fact is not an axiom of abstract OrderOneData. -/
theorem attachedSelectedPicture_edge_within_label_carrier
    (a : (I × Selected) ⊕ ActualEdge)
    (edge : ActualEdge) (he : edge ∈ (Out).edges a) :
    edge.1 ⊆ (Out).carrier a := by
  cases a with
  | inl iq =>
      exact he
  | inr actual =>
      change edge = actual at he
      subst edge
      exact Set.Subset.rfl

/-- An actual A-support edge contained in a chosen standard has a
real old A-support antecedent, whether its current output occurrence
label originally came from that standard or a foreign designated copy.
Physical carrier equality yields equality of real edge labels. -/
theorem attachedSelectedPicture_geometric_edge_pullback
    (i : I) (edge : ActualEdge)
    (hContained : edge.1 ⊆ copyCarrier (Std i)) :
    ∃ old : OldEdge, StdEdge i old = edge := by
  have hImage : edge.1 ⊆
      (fun x : X => Std i x) '' (Set.univ : Set X) := by
    intro z hz
    obtain ⟨x, hx⟩ := hContained hz
    exact ⟨x, Set.mem_univ x, hx⟩
  obtain ⟨old, _hOld, hImageEq⟩ :=
    oldACarrierEdge_pullback_of_subset_image
      A C.toRelStructure
      (RelStructure.Attachment.attach C.toRelStructure S R f)
      (Std i) Set.univ edge hImage
  refine ⟨old, ?_⟩
  apply Subtype.ext
  exact (actualAPictureEdgeEquiv_standard_carrier
    A hA C.toRelStructure S R f i old).trans hImageEq

/-- An arbitrary GEOMETRICALLY standard-owned output occurrence that
meets a wagon yields a genuine old edge with exactly that OUTPUT
wagon. This avoids changing the occurrence's designated label. -/
theorem attachedSelectedPicture_geometric_wagon_source
    (i : I) (a : (I × Selected) ⊕ ActualEdge)
    (W : Quotient ((Train).wagonSetoid μ))
    (hContained : (Out).carrier a ⊆ copyCarrier (Std i))
    (hMeets : (Out).Meets a W) :
    ∃ old : OldEdge, (Out).parent (StdEdge i old) = W := by
  obtain ⟨edge, hEdge, hW⟩ := hMeets
  have hSub : edge.1 ⊆ copyCarrier (Std i) :=
    (attachedSelectedPicture_edge_within_label_carrier
      A hA B D C family selected e R f T U hShared μ
      a edge hEdge).trans hContained
  obtain ⟨old, hOld⟩ :=
    attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i edge hSub
  refine ⟨old, ?_⟩
  rw [hOld]
  exact hW

include hRel

/-- Actual output wagon connector between DIFFERENT geometrically
owned standards: both physical incidence edges pull back to those
standards, and the generated wagon is one witness-core wagon with
genuine shared edges local to both Q_i and Q_j. No literal source
label equality is required. -/
theorem attachedSelectedPicture_geometric_wagon_two_standards
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i j : I) (hij : i ≠ j)
    (hW : K.connector k = Sum.inr W)
    (hLeft : owner k = Sum.inl i)
    (hRight : owner (cyclicSucc k) = Sum.inl j) :
    ∃ (oldA oldB : OldEdge)
      (c : Quotient (U.wagonSetoid μ)) (s t : SharedEdge),
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) oldA ∧
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S t) oldB ∧
      Quotient.mk (U.wagonSetoid μ) (Emb i s) = c ∧
      Quotient.mk (U.wagonSetoid μ) (Emb j t) = c ∧
      (Emb i s).1 ⊆ Set.range (f i) ∧
      (Emb j t).1 ⊆ Set.range (f j) := by
  obtain ⟨edgeA, edgeB, hEdgeA, hWA, hEdgeB, hWB⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hContainedA : (Out).carrier (K.label k) ⊆
      copyCarrier (Std i) := by
    have h := hAllowed k
    rw [hLeft] at h
    exact h
  have hContainedB : (Out).carrier (K.label (cyclicSucc k)) ⊆
      copyCarrier (Std j) := by
    have h := hAllowed (cyclicSucc k)
    rw [hRight] at h
    exact h
  obtain ⟨oldA, hParentA⟩ := attachedSelectedPicture_geometric_wagon_source
    A hA B D C family selected e R f T U hShared μ
    i (K.label k) W hContainedA ⟨edgeA, hEdgeA, hWA⟩
  obtain ⟨oldB, hParentB⟩ := attachedSelectedPicture_geometric_wagon_source
    A hA B D C family selected e R f T U hShared μ
    j (K.label (cyclicSucc k)) W hContainedB ⟨edgeB, hEdgeB, hWB⟩
  have hSame : (Train).rel μ (StdEdge i oldA) (StdEdge j oldB) :=
    Quotient.exact (hParentA.trans hParentB.symm)
  obtain ⟨c, s, t, hsOld, htOld, hsCore, htCore, hsLocal, htLocal⟩ :=
    generatedActualASupportTrain_cross_standard_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ
      i j hij oldA oldB hSame
  exact ⟨oldA, oldB, c, s, t,
    hsOld, htOld, hsCore, htCore, hsLocal, htLocal⟩

/-- The standard/core wagon case for GEOMETRIC ownership: a physical
support edge from the chosen standard and the actual singleton core
edge have one wagon, yielding a genuine shared old/core edge in Q_i. -/
theorem attachedSelectedPicture_geometric_wagon_standard_core
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i : I) (b : CoreEdge)
    (hW : K.connector k = Sum.inr W)
    (hLeft : owner k = Sum.inl i)
    (hRight : owner (cyclicSucc k) = Sum.inr b) :
    ∃ (old : OldEdge) (s : SharedEdge),
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
      U.rel μ (Emb i s) b ∧
      (Emb i s).1 ⊆ Set.range (f i) := by
  obtain ⟨edgeA, edgeB, hEdgeA, hParentA, hEdgeB, hParentB⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hContained : (Out).carrier (K.label k) ⊆
      copyCarrier (Std i) := by
    have h := hAllowed k
    rw [hLeft] at h
    exact h
  obtain ⟨old, hParentOld⟩ := attachedSelectedPicture_geometric_wagon_source
    A hA B D C family selected e R f T U hShared μ
    i (K.label k) W hContained ⟨edgeA, hEdgeA, hParentA⟩
  have hCoreLabel : K.label (cyclicSucc k) = Sum.inr (CoreActual b) := by
    have h := hAllowed (cyclicSucc k)
    rw [hRight] at h
    exact h
  have hEqB : edgeB = CoreActual b := by
    rw [hCoreLabel] at hEdgeB
    change edgeB = CoreActual b at hEdgeB
    exact hEdgeB
  have hParentCore : (Out).parent (CoreActual b) = W := by
    rw [← hEqB]
    exact hParentB
  have hSame : (Train).rel μ (StdEdge i old) (CoreActual b) :=
    Quotient.exact (hParentOld.trans hParentCore.symm)
  obtain ⟨s, hsOld, hsCore, hsLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i old b hSame
  exact ⟨old, s, hsOld, hsCore, hsLocal⟩

/-- Reverse orientation of the geometric standard/core wagon contact. -/
theorem attachedSelectedPicture_geometric_wagon_core_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (i : I) (b : CoreEdge)
    (hW : K.connector k = Sum.inr W)
    (hLeft : owner k = Sum.inr b)
    (hRight : owner (cyclicSucc k) = Sum.inl i) :
    ∃ (old : OldEdge) (s : SharedEdge),
      T.rel μ (sharedOldACarrierInclusion A C.toRelStructure S s) old ∧
      U.rel μ (Emb i s) b ∧
      (Emb i s).1 ⊆ Set.range (f i) := by
  obtain ⟨edgeB, edgeA, hEdgeB, hParentB, hEdgeA, hParentA⟩ :=
    OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
  have hContained : (Out).carrier (K.label (cyclicSucc k)) ⊆
      copyCarrier (Std i) := by
    have h := hAllowed (cyclicSucc k)
    rw [hRight] at h
    exact h
  obtain ⟨old, hParentOld⟩ := attachedSelectedPicture_geometric_wagon_source
    A hA B D C family selected e R f T U hShared μ
    i (K.label (cyclicSucc k)) W hContained ⟨edgeA, hEdgeA, hParentA⟩
  have hCoreLabel : K.label k = Sum.inr (CoreActual b) := by
    have h := hAllowed k
    rw [hLeft] at h
    exact h
  have hEqB : edgeB = CoreActual b := by
    rw [hCoreLabel] at hEdgeB
    change edgeB = CoreActual b at hEdgeB
    exact hEdgeB
  have hParentCore : (Out).parent (CoreActual b) = W := by
    rw [← hEqB]
    exact hParentB
  have hSame : (Train).rel μ (StdEdge i old) (CoreActual b) :=
    Quotient.exact (hParentOld.trans hParentCore.symm)
  obtain ⟨s, hsOld, hsCore, hsLocal⟩ :=
    generatedActualASupportTrain_standard_core_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i old b hSame
  exact ⟨old, s, hsOld, hsCore, hsLocal⟩

/-- Both geometric singleton core-edge labels meet the same output
wagon. Exact restriction to the core returns their witness relation. -/
theorem attachedSelectedPicture_geometric_wagon_core_core
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (W : Quotient ((Train).wagonSetoid μ))
    (b c : CoreEdge)
    (hW : K.connector k = Sum.inr W)
    (hLeft : owner k = Sum.inr b)
    (hRight : owner (cyclicSucc k) = Sum.inr c) :
    U.rel μ b c := by
  have hLabelB : K.label k = Sum.inr (CoreActual b) := by
    have h := hAllowed k
    rw [hLeft] at h
    exact h
  have hLabelC : K.label (cyclicSucc k) = Sum.inr (CoreActual c) := by
    have h := hAllowed (cyclicSucc k)
    rw [hRight] at h
    exact h
  exact attachedSelectedPicture_cycle_wagon_core_core_relation
    A hA B D C family selected e R f T U hShared hRel μ
    K k W b c hW hLabelB hLabelC

end GeometricSelectedCycleWagon
end StructuralRamsey.Girth
