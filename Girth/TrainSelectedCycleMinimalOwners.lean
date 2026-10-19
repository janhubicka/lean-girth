import Girth.TrainMinimalCyclicOwners
import Girth.TrainSelectedPictureOutputLabelCover

/-!
# Circulation: actual selected-output cycles admit minimal legal owner assignments

The minimum segmentation in Section 12 must be chosen among ALL allowed
representations of a physical occurrence. Designated labels have their
actual standard index; private physical edges have a unique standard
owner; shared edges may legitimately be treated as a core singleton or
as part of a standard. Choosing the canonical edge provenance as the
segmentation in advance need not minimize the number of segments.

This module combines the checked exhaustive physical source-label
theorem with the general cyclic-minimizer theorem. It gives a minimal
occurrence-wise assignment for an ACTUAL selected-picture BigCycle,
not merely for an abstract owner predicate.

A singleton core-edge assignment cannot occupy two adjacent
occurrences, because BigCycle requires adjacent labels to differ.
A designated occurrence can only be assigned to its actual standard.

These are source/owner facts only. Constructing the cyclic segment
blocks and the witness BigCycle, proving connector injectivity, and
transferring A1--A3 remain separate obligations. No appendix input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section MinimalActualSelectedOwners

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
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) I b))

/-- Exact admissibility of a source owner for one real selected-picture
output label. Unlike canonical core/private provenance, a shared edge
may have MULTIPLE permitted standard or core owners. -/
def selectedOutputOwnerAllowed
    (a : (I × Selected) ⊕ ActualEdge) (owner : I ⊕ CoreEdge) : Prop :=
  match owner with
  | .inl i => ∃ old : Label, a = LabelMap i old
  | .inr b => a = Sum.inr (CoreActual b)

local notation "Allowed" => selectedOutputOwnerAllowed
  A hA B D C family selected e R f

/-- There is a genuinely minimal occurrence-wise provenance assignment
for EVERY actual selected-picture output big cycle. No finiteness of
the standard-index or core-edge types is used. The number of cyclic
source changes is minimized among all admissible assignments. -/
theorem attachedSelectedPicture_cycle_exists_minimal_owners
    {n : ℕ} (K : (Out).BigCycle n) :
    ∃ owner : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, Allowed (K.label k) (owner k)) ∧
      (∀ other : Fin n → I ⊕ CoreEdge,
        (∀ k : Fin n, Allowed (K.label k) (other k)) →
        cyclicOwnerChanges owner ≤ cyclicOwnerChanges other) := by
  have hNonempty (k : Fin n) :
      ∃ owner : I ⊕ CoreEdge, Allowed (K.label k) owner := by
    rcases attachedSelectedPicture_cycle_every_label_has_source
      A hA B D C family selected e R f T U hShared μ K k with
      ⟨i, old, hLabel⟩ | ⟨b, hLabel⟩
    · exact ⟨.inl i, ⟨old, hLabel⟩⟩
    · exact ⟨.inr b, hLabel⟩
  exact exists_minimal_cyclic_owner
    (fun k owner => Allowed (K.label k) owner) hNonempty

/-- If EVERY actual output label already comes from one fixed
standard, a minimal admissible assignment has no cyclic owner changes.
This is the precise one-standard alternative to multi-segment
witness reduction; it does not assume the standard owner was unique. -/
theorem attachedSelectedPicture_cycle_minimal_zero_of_one_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (i : I)
    (hOne : ∀ k : Fin n, ∃ old : Label,
      K.label k = LabelMap i old) :
    ∃ owner : Fin n → I ⊕ CoreEdge,
      (∀ k : Fin n, Allowed (K.label k) (owner k)) ∧
      cyclicOwnerChanges owner = 0 := by
  obtain ⟨owner, hAllowed, hMinimal⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_owners
      A hA B D C family selected e R f T U hShared μ K
  have hConstAllowed : ∀ k : Fin n,
      Allowed (K.label k) (Sum.inl i) := by
    intro k
    exact hOne k
  have hConstZero :
      cyclicOwnerChanges
        (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge)) = 0 :=
    (cyclicOwnerChanges_eq_zero_iff
      (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge))).2
        (by intro j; rfl)
  refine ⟨owner, hAllowed, ?_⟩
  have hBound := hMinimal
    (fun _ : Fin n => (Sum.inl i : I ⊕ CoreEdge)) hConstAllowed
  rw [hConstZero] at hBound
  exact Nat.eq_zero_of_le_zero hBound

/-- A genuine core-edge singleton owner cannot own two successive
occurrences in the actual output cycle: its image is one fixed physical
edge label, and consecutive BigCycle labels are distinct. -/
theorem attachedSelectedPicture_core_owner_singleton_boundary
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, Allowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge)
    (hCore : owner k = Sum.inr b) :
    owner (cyclicSucc k) ≠ Sum.inr b := by
  intro hNext
  have hHere := hAllowed k
  have hThere := hAllowed (cyclicSucc k)
  rw [hCore] at hHere
  rw [hNext] at hThere
  change K.label k = Sum.inr (CoreActual b) at hHere
  change K.label (cyclicSucc k) = Sum.inr (CoreActual b) at hThere
  exact K.adjacent_ne k (hHere.trans hThere.symm)

/-- A witness-core edge source forms a singleton cyclic segment:
neither cyclic neighbour can carry the same core-edge owner. This
uses the real cycle's two-occurrence lower bound, including wraparound. -/
theorem attachedSelectedPicture_core_owner_isolated
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, Allowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge)
    (hCore : owner k = Sum.inr b) :
    owner (trainCyclicPred k) ≠ Sum.inr b ∧
    owner (cyclicSucc k) ≠ Sum.inr b := by
  constructor
  · intro hPrev
    have hDifferent :=
      attachedSelectedPicture_core_owner_singleton_boundary
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed (trainCyclicPred k) b hPrev
    rw [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two k]
      at hDifferent
    exact hDifferent hCore
  · exact attachedSelectedPicture_core_owner_singleton_boundary
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k b hCore

/-- A designated output label carries its standard index literally.
No admissible minimizer can reassign it to the core or to a different
standard, independently of geometric containment elsewhere. -/
theorem attachedSelectedPicture_designated_owner_index
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, Allowed (K.label k) (owner k))
    (k : Fin n) (i : I) (q : Selected)
    (hLabel : K.label k = Sum.inl (i, q)) :
    owner k = Sum.inl i := by
  have hSource := hAllowed k
  cases hOwner : owner k with
  | inl j =>
      rw [hOwner] at hSource
      change ∃ old : Label, K.label k = LabelMap j old at hSource
      obtain ⟨old, hEq⟩ := hSource
      cases old with
      | inl p =>
          change K.label k = Sum.inl (j, p) at hEq
          have hij : j = i := by
            have hPair := Sum.inl.inj (hEq.symm.trans hLabel)
            exact congrArg Prod.fst hPair
          simpa [hOwner, hij]
      | inr a =>
          change K.label k = Sum.inr _ at hEq
          rw [hLabel] at hEq
          cases hEq
  | inr b =>
      rw [hOwner] at hSource
      change K.label k = Sum.inr (CoreActual b) at hSource
      rw [hLabel] at hSource
      cases hSource

end MinimalActualSelectedOwners

end StructuralRamsey.Girth
