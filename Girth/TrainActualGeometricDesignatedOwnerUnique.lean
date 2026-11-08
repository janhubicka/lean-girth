import Girth.TrainSelectedPictureLabelEquiv
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Geometric owner of a genuine two-edge designated output copy is unique

The actual geometric owner relation permits assigning a whole labelled
carrier to ANY standard that contains it. For an arbitrary selected
copy this can be more permissive than literal source-standard ownership.

Under the final circulation hypotheses (each selected B-copy has at
least two distinct physical A-support edges and its prescribed base
image is A-strong), the checked private-vertex theorem constructs a
point OUTSIDE the active gluing subsystem. A private point of standard
i cannot lie in standard j unless i=j.

The existing exact private-standard index theorem handles EQUALITY
of images. Here we derive the needed SUBSET version by restricting
the receiving standard's source carrier to the inverse image of
the whole selected image. No new attachment axiom is required.
Consequently every geometric standard owner of an ACTUAL designated
output occurrence is its LITERAL original standard index.

This may simplify positive two-cut sources; it does NOT imply that
arbitrary physical edge labels have unique standards, and no global
supreme-cycle theorem is claimed. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section PrivateStandardOwnerSubset

variable {L : RelLanguage.{u}} {X Y I : Type v}

/-- A private vertex in a subcarrier of one attached standard
prevents its WHOLE image from being contained in another standard.
Use the checked exact-image private-index theorem after taking the
receiving standard's inverse-image carrier. -/
theorem attachment_privateStandardCarrier_subset_index
    (B : RelStructure L X) (S : Set X) (D : RelStructure L Y)
    (f : I → Embedding (B.induce S) D)
    (i j : I) (Q : Set X)
    (hPrivate : ∃ x, x ∈ Q ∧ x ∉ S)
    (hContain :
      (fun x : X => RelStructure.Attachment.copyEmbedding B S D f i x) '' Q ⊆
        copyCarrier (RelStructure.Attachment.copyEmbedding B S D f j)) :
    i = j := by
  let std : I → X → RelStructure.Attachment.Vertex S (W := Y) (I := I) :=
    fun k x => RelStructure.Attachment.copyEmbedding B S D f k x
  let Qj : Set X := (std j) ⁻¹' ((std i) '' Q)
  have hCarrier : (std i) '' Q = (std j) '' Qj := by
    ext z
    constructor
    · intro hz
      have hzj : z ∈ copyCarrier
          (RelStructure.Attachment.copyEmbedding B S D f j) :=
        hContain hz
      rcases hzj with ⟨y, rfl⟩
      exact ⟨y, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  exact attachment_privateStandardCarrier_unique_index
    B S D f i j Q Qj hPrivate hCarrier

end PrivateStandardOwnerSubset

section ActualDesignatedGeometricOwner

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- No foreign geometric standard owner of a genuine selected output
designated label under the actual old base strongness and two-edge
target hypotheses. The physical image must remain in its own
standard, not merely be equal to another carrier set. -/
theorem attachedSelectedPicture_designated_geometric_standard_unique
    [Finite UA]
    (hBaseStrong : ∀ q : Selected,
      AStrong A D (copyCarrier q.1.base))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (i j : I) (q : Selected)
    (hGeom : GeomAllowed (Sum.inl (i, q)) (Sum.inl j)) :
    i = j := by
  change
    (fun x : X => Std i x) '' copyCarrier q.1.embedding ⊆
      copyCarrier (Std j) at hGeom
  exact attachment_privateStandardCarrier_subset_index
    C.toRelStructure S R f i j (copyCarrier q.1.embedding)
    (selectedCopy_private_vertex_of_two_edges
      A B D C family selected e q (hBaseStrong q) (hTwo q))
    hGeom

/-- At an actual cyclic output occurrence, an admissible geometric
standard owner of a selected designated label must be its literal
standard source. No minimality of the owner assignment is needed. -/
theorem attachedSelectedPicture_designated_occurrence_owner_eq
    [Finite UA]
    (hBaseStrong : ∀ q : Selected,
      AStrong A D (copyCarrier q.1.base))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ OldACarrierEdge A R)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (i j : I) (q : Selected)
    (hLabel : K.label k = Sum.inl (i, q))
    (hOwner : owner k = Sum.inl j) :
    i = j := by
  have h := hAllowed k
  rw [hLabel, hOwner] at h
  exact attachedSelectedPicture_designated_geometric_standard_unique
    A hA B D C family selected e R f T U hShared μ
    hBaseStrong hTwo i j q h

end ActualDesignatedGeometricOwner

end StructuralRamsey.Girth
