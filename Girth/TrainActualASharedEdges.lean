import Girth.ForestActualACopyOwner
import Girth.AttachmentGeometry

/-!
# Exactly which old A-edges become core edges in the real attachment?

A physical old A-support edge in a standard picture is identified
with a CORE A-support edge if and only if every vertex of that
old A-copy lies in the genuine gluing subsystem S.

One direction uses the actual attachment's private/core vertex
disjointness (not a claim about equal wagon carriers). The other
uses the checked copy_extends property to factor the full A-copy
through the core embedding. This supplies the missing concrete
SHARED-edge criterion for relating the actual relational support
hypergraph to a formal physical edge pushout.

No designated-copy coverage or edge pruning is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- An old A-copy transported to standard picture i has every
physical vertex in the core exactly when the complete old
A-copy carrier lies in the gluing subsystem. -/
theorem attached_standardACopy_subset_core_iff
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (aOld : RelStructure.Embedding A B) :
    copyCarrier
      ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld)
      ⊆ copyCarrier (RelStructure.Attachment.coreEmbedding B S D f)
    ↔ ∀ u : UA, aOld u ∈ S := by
  constructor
  · intro h u
    have hu :
        ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld) u ∈
          copyCarrier (RelStructure.Attachment.coreEmbedding B S D f) :=
      h ⟨u, rfl⟩
    obtain ⟨y, hy⟩ := hu
    have hEq :
        RelStructure.Attachment.copyMap B S D f i (aOld u) =
          Sum.inl y := by
      exact hy.symm
    exact RelStructure.Attachment.mem_of_copyMap_eq_inl hEq
  · intro hRange
    rintro z ⟨u, hu⟩
    refine ⟨f i ⟨aOld u, hRange u⟩, ?_⟩
    change
      RelStructure.Attachment.coreEmbedding B S D f
          (f i ⟨aOld u, hRange u⟩) = z
    calc
      RelStructure.Attachment.coreEmbedding B S D f
          (f i ⟨aOld u, hRange u⟩) =
        RelStructure.Attachment.copyEmbedding B S D f i (aOld u) :=
          (RelStructure.Attachment.copy_extends B S D f i
            ⟨aOld u, hRange u⟩).symm
      _ = z := hu

/-- The standard A-edge is precisely a transported CORE A-edge
if and only if it is entirely in the true active gluing subsystem.
This is equality of whole support edges, not merely inclusion
of one or two boundary vertices. -/
theorem attached_standardACopy_is_shared_iff
    (A : RelStructure L UA)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (aOld : RelStructure.Embedding A B) :
    (∃ aCore : RelStructure.Embedding A D,
      copyCarrier
        ((RelStructure.Attachment.copyEmbedding B S D f i).comp aOld) =
      copyCarrier
        ((RelStructure.Attachment.coreEmbedding B S D f).comp aCore))
    ↔ ∀ u : UA, aOld u ∈ S := by
  classical
  let std : RelStructure.Embedding B
      (RelStructure.Attachment.attach B S D f) :=
    RelStructure.Attachment.copyEmbedding B S D f i
  let core : RelStructure.Embedding D
      (RelStructure.Attachment.attach B S D f) :=
    RelStructure.Attachment.coreEmbedding B S D f
  constructor
  · rintro ⟨aCore, hSame⟩
    have hSubset :
        copyCarrier (std.comp aOld) ⊆ copyCarrier core := by
      intro z hz
      rw [hSame] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨aCore u, hu⟩
    exact (attached_standardACopy_subset_core_iff
      A B S D f i aOld).mp hSubset
  · intro hRange
    have hSubset :
        copyCarrier (std.comp aOld) ⊆ copyCarrier core :=
      (attached_standardACopy_subset_core_iff
        A B S D f i aOld).mpr hRange
    have hInside : ∀ u : UA,
        ∃ y : Core, (std.comp aOld) u = core y := by
      intro u
      obtain ⟨y, hy⟩ := hSubset ⟨u, rfl⟩
      exact ⟨y, hy.symm⟩
    let aCore : RelStructure.Embedding A D :=
      (std.comp aOld).factorThroughRange core hInside
    have hEq : core.comp aCore = std.comp aOld := by
      apply RelStructure.Embedding.ext
      intro u
      exact (Classical.choose_spec (hInside u)).symm
    refine ⟨aCore, ?_⟩
    rw [hEq]

end StructuralRamsey.Girth
