import Girth.TrainSelectedPictureContainedBlocks

/-!
# Circulation: two supported edges exclude foreign standard ownership

A designated copy from standard j whose ENTIRE geometric carrier lies
in a different standard i must have its old A-support inside the
active subsystem. Strong boundary classification then forces every
vertex of this copy into EACH of its supported A-edges. Two finite
A-copies cannot have properly nested carriers, so all such support
edges are equal.

This closes the SUPPORT-UNIQUENESS subargument noted in the
one-standard circulation case. It does not resolve the one-edge
target, preserve designation by a mixed replacement, or transfer a
full selected BigCycle into a standard. No appendix input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section ForeignDesignatedSupport

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (e : RelStructure.Embedding A D)

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure

/-- If a designated B-copy is wholly in the active subsystem, all its
supported old A-edges coincide. The finite-carrier antichain principle
is used only in the last step. -/
theorem designated_active_source_edges_eq [Finite UA]
    (q : DesignatedCopy B D C family)
    (hStrong : AStrong A D (copyCarrier q.base))
    (hActive : copyCarrier q.embedding ⊆ S)
    (r s : OldEdge)
    (hr : r.1 ⊆ copyCarrier q.embedding)
    (hs : s.1 ⊆ copyCarrier q.embedding) :
    r = s := by
  have hsr : s.1 ⊆ r.1 := by
    intro x hx
    exact designated_active_vertex_mem_source_edge
      A B D C family e q hStrong hActive r hr x (hs hx)
  exact (oldACarrierEdge_eq_of_subset A C.toRelStructure s r hsr).symm

end ForeignDesignatedSupport

section ForeignStandard

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f

/-- A designated copy originally attached at j, but geometrically
contained in another standard i, supports at most one old A-edge.
The proof does not relabel the designated occurrence. -/
theorem foreign_designated_source_edges_eq [Finite UA]
    (q : DesignatedCopy B D C family)
    (j i : I) (hji : j ≠ i)
    (hStrong : AStrong A D (copyCarrier q.base))
    (hContained :
      (fun x : X => Std j x) '' copyCarrier q.embedding ⊆
        copyCarrier (Std i))
    (r s : OldEdge)
    (hr : r.1 ⊆ copyCarrier q.embedding)
    (hs : s.1 ⊆ copyCarrier q.embedding) :
    r = s := by
  have hActive : copyCarrier q.embedding ⊆ S := by
    intro w hw
    have hOther : Std j w ∈ copyCarrier (Std i) :=
      hContained ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := hOther
    by_contra hwNot
    have hMaps :
        RelStructure.Attachment.copyMap C.toRelStructure S R f j w =
          RelStructure.Attachment.copyMap C.toRelStructure S R f i v := hv.symm
    exact hji (RelStructure.Attachment.index_eq_of_outside hwNot hMaps)
  exact designated_active_source_edges_eq
    A B D C family e q hStrong hActive r s hr hs

/-- Two DISTINCT old support A-edges prohibit assignment of a
designated occurrence to a different geometric standard. This is
the non-one-edge branch of the one-standard circulation obstruction. -/
theorem foreign_designated_two_edges_not_contained [Finite UA]
    (q : DesignatedCopy B D C family)
    (j i : I) (hji : j ≠ i)
    (hStrong : AStrong A D (copyCarrier q.base))
    (r s : OldEdge)
    (hr : r.1 ⊆ copyCarrier q.embedding)
    (hs : s.1 ⊆ copyCarrier q.embedding)
    (hrs : r ≠ s) :
    ¬ ((fun x : X => Std j x) '' copyCarrier q.embedding ⊆
        copyCarrier (Std i)) := by
  intro hContained
  exact hrs (foreign_designated_source_edges_eq
    A B D C family e R f q j i hji hStrong hContained r s hr hs)

end ForeignStandard
end StructuralRamsey.Girth
