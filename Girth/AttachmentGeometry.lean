import Girth.ActivePicture
import Girth.Support
import PartiteConstruction.Relational.Attachment

/-! # Geometry of free picture attachments

This module isolates the set-theoretic geometry of the standard picture
extension.  It is independent of the Ramsey argument: every attached copy
meets the core exactly in its prescribed gluing subsystem, and two distinct
attached copies meet exactly where their gluing subsystems meet in the core.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W I : Type v}

/-- One standard copy meets the core exactly in the image of its gluing
subsystem. -/
theorem attachment_copy_core_intersection
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D) (i : I) :
    copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) ∩
        copyCarrier (RelStructure.Attachment.coreEmbedding B S D f) =
      copyCarrier
        ((RelStructure.Attachment.coreEmbedding B S D f).comp (f i)) := by
  classical
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hEq :
        RelStructure.Attachment.copyMap B S D f i x = Sum.inl y :=
      hx.trans hy.symm
    have hxS : x ∈ S :=
      RelStructure.Attachment.mem_of_copyMap_eq_inl hEq
    refine ⟨⟨x, hxS⟩, ?_⟩
    change Sum.inl (f i ⟨x, hxS⟩) = z
    exact
      (RelStructure.Attachment.copyMap_mem
          (B := B) (S := S) (D := D) (f := f) i x hxS).symm.trans hx
  · rintro ⟨x, hx⟩
    constructor
    · refine ⟨x.1, ?_⟩
      calc
        RelStructure.Attachment.copyEmbedding B S D f i x.1 =
            RelStructure.Attachment.coreEmbedding B S D f (f i x) :=
          RelStructure.Attachment.copy_extends B S D f i x
        _ = z := hx
    · exact ⟨f i x, hx⟩

/-- Two distinct standard copies meet exactly in the intersection of the two
gluing images inside the core. -/
theorem attachment_copy_copy_intersection
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D) {i j : I} (hij : i ≠ j) :
    copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) ∩
        copyCarrier (RelStructure.Attachment.copyEmbedding B S D f j) =
      copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp (f i)) ∩
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp (f j)) := by
  classical
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy :
        RelStructure.Attachment.copyMap B S D f i x =
          RelStructure.Attachment.copyMap B S D f j y :=
      hx.trans hy.symm
    have hxS : x ∈ S := by
      by_contra hxS
      exact hij
        (RelStructure.Attachment.index_eq_of_outside
          (B := B) (S := S) (D := D) (f := f) hxS hxy)
    have hxi :
        RelStructure.Attachment.copyMap B S D f i x =
          Sum.inl (f i ⟨x, hxS⟩) :=
      RelStructure.Attachment.copyMap_mem
        (B := B) (S := S) (D := D) (f := f) i x hxS
    have hyCore :
        RelStructure.Attachment.copyMap B S D f j y =
          Sum.inl (f i ⟨x, hxS⟩) :=
      hy.trans (hx.symm.trans hxi)
    have hyS : y ∈ S :=
      RelStructure.Attachment.mem_of_copyMap_eq_inl hyCore
    constructor
    · refine ⟨⟨x, hxS⟩, ?_⟩
      change Sum.inl (f i ⟨x, hxS⟩) = z
      exact hxi.symm.trans hx
    · refine ⟨⟨y, hyS⟩, ?_⟩
      change Sum.inl (f j ⟨y, hyS⟩) = z
      exact
        (RelStructure.Attachment.copyMap_mem
          (B := B) (S := S) (D := D) (f := f) j y hyS).symm.trans hy
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    constructor
    · refine ⟨x.1, ?_⟩
      calc
        RelStructure.Attachment.copyEmbedding B S D f i x.1 =
            RelStructure.Attachment.coreEmbedding B S D f (f i x) :=
          RelStructure.Attachment.copy_extends B S D f i x
        _ = z := hx
    · refine ⟨y.1, ?_⟩
      calc
        RelStructure.Attachment.copyEmbedding B S D f j y.1 =
            RelStructure.Attachment.coreEmbedding B S D f (f j y) :=
          RelStructure.Attachment.copy_extends B S D f j y
        _ = z := hy

/-- In particular distinct attached copies can meet only in the core. -/
theorem attachment_copy_copy_intersection_subset_core
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D) {i j : I} (hij : i ≠ j) :
    copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) ∩
        copyCarrier (RelStructure.Attachment.copyEmbedding B S D f j) ⊆
      copyCarrier (RelStructure.Attachment.coreEmbedding B S D f) := by
  intro z hz
  rw [attachment_copy_copy_intersection B S D f hij] at hz
  rcases hz.1 with ⟨x, hx⟩
  exact ⟨f i x, hx⟩

end StructuralRamsey.Girth
