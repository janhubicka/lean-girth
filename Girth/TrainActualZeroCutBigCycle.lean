import Girth.TrainActualZeroCutLabelPullback
import Girth.TrainActualStandardWagonMap

/-!
# Literal old BigCycle inside one actual attached standard

For any selected output BigCycle whose labels are geometrically
contained in one standard, the two-support-edge and A-strong
hypotheses give exact old source labels (without changing the
designated labels). Every physical connector also has a source:
vertex connectors belong to that attached standard; wagon connectors
come from its injected old wagon quotient.

The standard embedding and wagon quotient embedding reflect BOTH
types of incidence, so the old labels and connectors form a genuine
old BigCycle. The constructor transports exact label identity,
connector identity, adjacency and connector injectivity rather than
postulating old-cycle legality.

Applied to an actual ZERO-cut assignment, this gives a full legal
old BigCycle with exact physical images. Transferring A1--A3,
source system-Girth and global supreme copies is a separate step.
No appendix result is used.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ZeroCutOldBigCycle

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" =>
  OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f

include hRel

/-- The standard embedding and its injective old-wagon quotient map
reflect both vertex and wagon incidence for literal old labels. -/
theorem attachedSelectedPicture_standard_incident_pullback
    (i : I) (a : Label)
    (q : X ⊕ Quotient (T.wagonSetoid μ))
    (h : (Out).Incident (LabelMap i a)
      (Sum.map (Std i) (StdWagon i) q)) :
    (Old).Incident a q := by
  cases q with
  | inl x =>
      change Std i x ∈ (Out).carrier (LabelMap i a) at h
      rw [attachedSelectedPicture_carrier
        A hA B D C family selected e R f T U hShared μ i a] at h
      obtain ⟨y, hy, hEq⟩ := h
      have hyx : y = x := (Std i).injective hEq
      change x ∈ (Old).carrier a
      simpa [hyx] using hy
  | inr p =>
      change (Out).Meets (LabelMap i a) (StdWagon i p) at h
      obtain ⟨old, hOld, hParent⟩ :=
        (attachedSelectedPicture_meets_iff
          A hA B D C family selected e R f T U hShared μ
          i a (StdWagon i p)).mp h
      have hW :
          StdWagon i (Quotient.mk (T.wagonSetoid μ) old) =
            StdWagon i p := by
        rw [generatedActualASupportTrain_standardWagonEmbedding_mk]
        exact hParent
      have hp : Quotient.mk (T.wagonSetoid μ) old = p :=
        (StdWagon i).injective hW
      change (Old).Meets a p
      exact ⟨old, hOld, hp⟩

/-- Each genuine output connector has a literal old antecedent whenever
its incident output label is geometrically contained in the standard.
This includes physical wagons, not just vertex connectors. -/
theorem attachedSelectedPicture_standard_connector_preimage
    {n : ℕ} (K : (Out).BigCycle n)
    (i : I)
    (hContained : ∀ k : Fin n,
      (Out).carrier (K.label k) ⊆ copyCarrier (Std i))
    (k : Fin n) :
    ∃ q : X ⊕ Quotient (T.wagonSetoid μ),
      K.connector k = Sum.map (Std i) (StdWagon i) q := by
  cases hConnector : K.connector k with
  | inl x =>
      have hx : x ∈ (Out).carrier (K.label k) := by
        have h := K.left_incident k
        rw [hConnector] at h
        exact h
      obtain ⟨y, hy⟩ := hContained k hx
      refine ⟨Sum.inl y, ?_⟩
      simpa [hConnector, hy]
  | inr W =>
      have hMeets : (Out).Meets (K.label k) W := by
        have h := K.left_incident k
        rw [hConnector] at h
        exact h
      obtain ⟨p, hp⟩ :=
        attachedSelectedPicture_geometric_used_wagon_in_standard_range
          A hA B D C family selected e R f T U hShared hRel μ
          i (K.label k) W (hContained k) hMeets
      refine ⟨Sum.inr p, ?_⟩
      simpa [hConnector, hp]

/-- From genuine source-label and connector preimages, construct the
full legal old BigCycle inside the chosen standard, with exact labelled
physical image identities. No acceptability hypothesis is used. -/
theorem attachedSelectedPicture_oneStandard_oldBigCycle [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {n : ℕ} (K : (Out).BigCycle n)
    (i : I)
    (hContained : ∀ k : Fin n,
      (Out).carrier (K.label k) ⊆ copyCarrier (Std i)) :
    ∃ Z : (Old).BigCycle n,
      (∀ k : Fin n, LabelMap i (Z.label k) = K.label k) ∧
      (∀ k : Fin n,
        Sum.map (Std i) (StdWagon i) (Z.connector k) = K.connector k) := by
  classical
  have hLabelExists (k : Fin n) :
      ∃ a : Label, LabelMap i a = K.label k :=
    attachedSelectedPicture_standard_label_pullback
      A hA B D C family selected e R f T U hShared μ
      hStrong hTwo i (K.label k) (hContained k)
  let labels : Fin n → Label := fun k => Classical.choose (hLabelExists k)
  have hLabel (k : Fin n) : LabelMap i (labels k) = K.label k :=
    Classical.choose_spec (hLabelExists k)
  have hConnExists (k : Fin n) :
      ∃ q : X ⊕ Quotient (T.wagonSetoid μ),
        K.connector k = Sum.map (Std i) (StdWagon i) q :=
    attachedSelectedPicture_standard_connector_preimage
      A hA B D C family selected e R f T U hShared hRel μ
      K i hContained k
  let connectors : Fin n → X ⊕ Quotient (T.wagonSetoid μ) :=
    fun k => Classical.choose (hConnExists k)
  have hConn (k : Fin n) :
      K.connector k = Sum.map (Std i) (StdWagon i) (connectors k) :=
    Classical.choose_spec (hConnExists k)
  let Z : (Old).BigCycle n := {
    length_ge_two := K.length_ge_two
    label := labels
    connector := connectors
    adjacent_ne := by
      intro k heq
      apply K.adjacent_ne k
      calc
        K.label k = LabelMap i (labels k) := (hLabel k).symm
        _ = LabelMap i (labels (cyclicSucc k)) := congrArg (LabelMap i) heq
        _ = K.label (cyclicSucc k) := hLabel (cyclicSucc k)
    connector_injective := by
      intro j k hjk
      apply K.connector_injective
      calc
        K.connector j = Sum.map (Std i) (StdWagon i) (connectors j) := hConn j
        _ = Sum.map (Std i) (StdWagon i) (connectors k) :=
          congrArg (Sum.map (Std i) (StdWagon i)) hjk
        _ = K.connector k := (hConn k).symm
    left_incident := by
      intro k
      apply attachedSelectedPicture_standard_incident_pullback
        A hA B D C family selected e R f T U hShared hRel μ
        i (labels k) (connectors k)
      have h := K.left_incident k
      rw [← hLabel k, hConn k] at h
      exact h
    right_incident := by
      intro k
      apply attachedSelectedPicture_standard_incident_pullback
        A hA B D C family selected e R f T U hShared hRel μ
        i (labels (cyclicSucc k)) (connectors k)
      have h := K.right_incident k
      rw [← hLabel (cyclicSucc k), hConn k] at h
      exact h
  }
  refine ⟨Z, ?_, ?_⟩
  · intro k
    exact hLabel k
  · intro k
    exact (hConn k).symm

/-- The actual ZERO-cut output BigCycle has an old legal BigCycle
with EXACT literal labels and connector images inside a unique
standard, under the nontrivial selected-target hypothesis.
This does not yet transfer A1--A3 or supremeness. -/
theorem attachedSelectedPicture_zero_cut_oldBigCycle [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hZero : cyclicOwnerChanges owner = 0) :
    ∃ (i : I) (Z : (Old).BigCycle n),
      (∀ k : Fin n, LabelMap i (Z.label k) = K.label k) ∧
      (∀ k : Fin n,
        Sum.map (Std i) (StdWagon i) (Z.connector k) = K.connector k) := by
  obtain ⟨i, hOwner⟩ :=
    attachedSelectedPicture_zero_cut_standard
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed hZero
  obtain ⟨Z, hl, hc⟩ :=
    attachedSelectedPicture_oneStandard_oldBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwo K i (fun k => (hOwner k).2)
  exact ⟨i, Z, hl, hc⟩

end ZeroCutOldBigCycle
end StructuralRamsey.Girth
