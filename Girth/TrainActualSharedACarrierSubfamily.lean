import Girth.TrainActualASharedEdges
import Girth.ForestDesignatedBSupportTransport

/-!
# Exact shared-edge subfamily of the genuine old A-support hypergraph

The synthetic one-level train edge pushout accepts an injection
inOld : SharedEdges ↪ OldEdges. For the REAL relational picture,
OldEdges are actual A-copy CARRIERS, and SharedEdges are those
old A-copy carriers lying wholly in the gluing subsystem S.

This module gives the canonical injection and proves its image is
exactly the shared-support subset. In particular, its complement
consists of carriers with a genuinely private old vertex, not
missing designated gluing-copy labels.

An old edge lies in the image of this injection exactly when its
standard-picture physical image is a genuine core A-support edge.
The separate construction of its core wagon-label injection is
the next train-specific requirement.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- The physical old A-copy carrier is an edge LABEL, not an
embedding or its potentially nontrivial automorphism class. -/
def OldACarrierEdge
    (A : RelStructure L UA) (B : RelStructure L Old) :=
  {T : Set Old // T ∈ actualACopyCarriers A B}

/-- Shared old A-edges are exactly the real A-copy carriers with
ALL vertices in the current gluing subsystem. -/
def SharedOldACarrierEdge
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) :=
  {T : OldACarrierEdge A B // T.1 ⊆ S}

/-- Inclusion of genuine old shared A-support edges into ALL old
physical A-support edges. Injectivity is literal on carriers. -/
def sharedOldACarrierInclusion
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) :
    SharedOldACarrierEdge A B S ↪ OldACarrierEdge A B where
  toFun T := T.1
  inj' := by
    intro x y h
    exact Subtype.ext h

/-- Exact characterization of shared labels: no equal-carrier
shortcut or designated-copy coverage is used. -/
theorem oldACarrier_mem_shared_range_iff
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) (T : OldACarrierEdge A B) :
    T ∈ Set.range (sharedOldACarrierInclusion A B S) ↔ T.1 ⊆ S := by
  constructor
  · rintro ⟨U, hU⟩
    have hUT : U.1 = T :=
      hU
    simpa [← hUT] using U.2
  · intro h
    refine ⟨⟨T, h⟩, rfl⟩

/-- An old A-edge is PRIVATE precisely when its actual carrier
contains an off-subsystem vertex. -/
theorem oldACarrier_not_shared_iff_private
    (A : RelStructure L UA) (B : RelStructure L Old)
    (S : Set Old) (T : OldACarrierEdge A B) :
    T ∉ Set.range (sharedOldACarrierInclusion A B S) ↔
      ∃ x : Old, x ∈ T.1 ∧ x ∉ S := by
  classical
  constructor
  · intro h
    by_contra hNo
    have hSubset : T.1 ⊆ S := by
      intro x hx
      by_contra hxNot
      exact hNo ⟨x, hx, hxNot⟩
    exact h ((oldACarrier_mem_shared_range_iff A B S T).mpr hSubset)
  · rintro ⟨x, hx, hxNot⟩ h
    exact hxNot ((oldACarrier_mem_shared_range_iff A B S T).mp h hx)

/-- A physical old A-edge maps to an actual CORE A-support under
a standard embedding iff it is one of the genuine shared old edges.
This identifies the precise shared support-edge subfamily for
the future edge-pushout comparison. -/
theorem oldACarrier_shared_iff_actual_core
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (T : OldACarrierEdge A B) :
    T ∈ Set.range (sharedOldACarrierInclusion A B S) ↔
      ∃ aCore : RelStructure.Embedding A D,
        ((fun x : Old =>
          (RelStructure.Attachment.copyEmbedding B S D f i) x) ''
            T.1) =
          copyCarrier
            ((RelStructure.Attachment.coreEmbedding B S D f).comp aCore) := by
  obtain ⟨aOld, hOld⟩ := T.2
  have hSupport :
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) ''
          T.1) =
      copyCarrier
        ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld) := by
    rw [hOld]
    exact (copyCarrier_comp_eq_image
      (RelStructure.Attachment.copyEmbedding B S D f i) aOld).symm
  constructor
  · intro hShared
    have hSubset : T.1 ⊆ S :=
      (oldACarrier_mem_shared_range_iff A B S T).mp hShared
    have hRange : ∀ u : UA, aOld u ∈ S := by
      intro u
      exact hSubset (by rw [hOld]; exact ⟨u, rfl⟩)
    obtain ⟨aCore, hCore⟩ :=
      (attached_standardACopy_is_shared_iff A B S D f i aOld).mpr hRange
    exact ⟨aCore, hSupport.trans hCore⟩
  · rintro ⟨aCore, hEqual⟩
    have hActual :
        copyCarrier
          ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld) =
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp aCore) :=
      hSupport.symm.trans hEqual
    have hRange : ∀ u : UA, aOld u ∈ S :=
      (attached_standardACopy_is_shared_iff A B S D f i aOld).mp
        ⟨aCore, hActual⟩
    apply (oldACarrier_mem_shared_range_iff A B S T).mpr
    intro x hx
    rw [hOld] at hx
    obtain ⟨u, rfl⟩ := hx
    exact hRange u

end StructuralRamsey.Girth
