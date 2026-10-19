import Girth.TrainSelectedCycleMinimalOwners

/-!
# Circulation: minimum GEOMETRIC occurrence owners on actual selected cycles

Literal source-label provenance is insufficient for a minimum
segmentation: an output designated label may be geometrically
contained in a standard other than the one recording its source.
The source-owner minimizer therefore need not minimize among all
standard-copy carrier containment choices.

At a fixed actual selected-picture cut, declare a standard owner
admissible precisely when the entire physical carrier of the output
label lies in that standard. A singleton witness-core edge is admissible
only for its literal physical edge label. The checked actual
source-label cover and exact carrier-transport formula prove this
more generous geometric admissibility is nonempty at EVERY
occurrence. The generic finite-cyclic minimizer therefore yields
a true minimum among these GEOMETRIC containment assignments,
without finiteness of the owner types.

This is still a predecessor of the witness reduct: it does NOT
construct maximal cyclic runs, identify their witness-copy indices,
certify connector contraction, or transfer A1--A3. Foreign designated
labels inside a standard need the separate mixed-localization lemma
to recover their physical incidence edges. No appendix is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section GeometricOwnerOfSelectedCycles

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "LiteralAllowed" => selectedOutputOwnerAllowed
  A hA B D C family selected e R f

/-- A geometric occurrence owner. The standard alternative requires
PHYSICAL CARRIER CONTAINMENT, not identical original source labels.
A core singleton still names exactly one physical core-edge label. -/
def selectedOutputGeometricOwnerAllowed
    (a : (I × Selected) ⊕ ActualEdge) (owner : I ⊕ CoreEdge) : Prop :=
  match owner with
  | .inl i => (Out).carrier a ⊆ copyCarrier (Std i)
  | .inr b => a = Sum.inr (CoreActual b)

local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- Every literal standard/core representation is an admissible
GEOMETRIC owner: exact selected-picture carrier transport places an
old label's entire carrier inside its actual attached standard. -/
theorem selectedOutput_literal_owner_geometric
    (a : (I × Selected) ⊕ ActualEdge)
    (owner : I ⊕ CoreEdge)
    (hLiteral : LiteralAllowed a owner) :
    GeomAllowed a owner := by
  cases owner with
  | inl i =>
      change ∃ old : Label, a = LabelMap i old at hLiteral
      obtain ⟨old, hEq⟩ := hLiteral
      change (Out).carrier a ⊆ copyCarrier (Std i)
      rw [hEq, attachedSelectedPicture_carrier
        A hA B D C family selected e R f T U hShared μ i old]
      intro z hz
      obtain ⟨x, _hx, hx⟩ := hz
      exact ⟨x, hx⟩
  | inr b =>
      change a = Sum.inr (CoreActual b) at hLiteral
      exact hLiteral

/-- Every ACTUAL selected-picture BigCycle has an admissible geometric
assignment minimizing the number of cyclic owner changes, even if
different standards share carriers and even for infinite owner types.
This is the geometric existence part of the minimum-segmentation step;
it does not construct the reduced witness's cyclic word. -/
theorem attachedSelectedPicture_cycle_exists_minimal_geometric_owners
    {n : ℕ} (K : (Out).BigCycle n) :
    ∃ owner : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, GeomAllowed (K.label k) (owner k)) ∧
      (∀ other : Fin n → I ⊕ CoreEdge,
        (∀ k : Fin n, GeomAllowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) := by
  obtain ⟨literalOwner, hLiteral, _hMinLiteral⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_owners
      A hA B D C family selected e R f T U hShared μ K
  have hExists (k : Fin n) :
      ∃ owner : I ⊕ CoreEdge,
        GeomAllowed (K.label k) owner := by
    exact ⟨literalOwner k,
      selectedOutput_literal_owner_geometric
        A hA B D C family selected e R f T U hShared μ
        (K.label k) (literalOwner k) (hLiteral k)⟩
  exact exists_minimal_cyclic_owner
    (fun k owner => GeomAllowed (K.label k) owner) hExists

/-- Core-edge singleton owners remain isolated even for the BROADER
geometric assignment. This is an actual BigCycle label-distinctness
fact, and handles cyclic last-to-first adjacency in both directions. -/
theorem attachedSelectedPicture_geometric_core_owner_isolated
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge)
    (hCore : owner k = Sum.inr b) :
    owner (trainCyclicPred k) ≠ Sum.inr b ∧
    owner (cyclicSucc k) ≠ Sum.inr b := by
  have hLabel : K.label k = Sum.inr (CoreActual b) := by
    have h := hAllowed k
    rw [hCore] at h
    exact h
  have hNext : owner (cyclicSucc k) ≠ Sum.inr b := by
    intro heq
    have h := hAllowed (cyclicSucc k)
    rw [heq] at h
    change K.label (cyclicSucc k) = Sum.inr (CoreActual b) at h
    exact K.adjacent_ne k (hLabel.trans h.symm)
  constructor
  · intro heq
    have h := hAllowed (trainCyclicPred k)
    rw [heq] at h
    change K.label (trainCyclicPred k) =
      Sum.inr (CoreActual b) at h
    have hDifferent := K.adjacent_ne (trainCyclicPred k)
    rw [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two k]
      at hDifferent
    exact hDifferent (h.trans hLabel.symm)
  · exact hNext

/-- A designated occurrence can never be assigned a core-edge owner,
even for the broader geometric admissibility relation. Its standard
owner need not be its LITERAL source standard. -/
theorem attachedSelectedPicture_geometric_designated_has_standard_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (i : I) (q : Selected)
    (hLabel : K.label k = Sum.inl (i, q)) :
    ∃ j : I, owner k = Sum.inl j := by
  have h := hAllowed k
  cases ho : owner k with
  | inl j =>
      exact ⟨j, ho⟩
  | inr b =>
      rw [ho] at h
      change K.label k = Sum.inr (CoreActual b) at h
      rw [hLabel] at h
      cases h

end GeometricOwnerOfSelectedCycles

end StructuralRamsey.Girth
