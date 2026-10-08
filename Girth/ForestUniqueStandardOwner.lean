import Girth.AttachmentGeometry
import Girth.UntouchedOwner

/-!
# Unique standard-copy owner outside the active core

In a free picture attachment, distinct standard copies intersect only
inside the attached core. Hence any vertex set containing at least one
noncore point and lying in a standard copy has a UNIQUE standard-copy
owner. Combined with the existing irreducible core-or-copy lemma, this
gives existence and uniqueness for every irreducible B-copy not
contained in the core.

The active-core case remains intentionally excluded: a copy completely
inside the core may be contained in several standard copies. This
is why arbitrary owner selection does not yet yield coherent parent
maps through the entire train genealogy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA V W I : Type v}

/-- A vertex set not contained in the core cannot lie in two distinct
standard copies. No irreducibility hypothesis is needed for uniqueness. -/
theorem attachment_unique_standard_owner_off_core
    (B : RelStructure L V)
    (S : Set V)
    (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (T : Set (RelStructure.Attachment.Vertex S (W := W) (I := I)))
    (hNotCore :
      ¬ T ⊆ copyCarrier
        (RelStructure.Attachment.coreEmbedding B S D f))
    {i j : I}
    (hi : T ⊆
      copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i))
    (hj : T ⊆
      copyCarrier (RelStructure.Attachment.copyEmbedding B S D f j)) :
    i = j := by
  by_contra hij
  apply hNotCore
  intro x hx
  have hPair :
      x ∈
        copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) ∩
          copyCarrier (RelStructure.Attachment.copyEmbedding B S D f j) :=
    ⟨hi hx, hj hx⟩
  exact
    attachment_copy_copy_intersection_subset_core
      B S D f hij hPair

/-- An irreducible copy not contained in the core has an actual,
unique standard-copy owner. Existence uses the verified
core-or-copy property of free relational attachments. -/
theorem attachment_irreducible_unique_owner_off_core
    (A : RelStructure L UA)
    (B : RelStructure L V)
    (S : Set V)
    (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (hA : A.Irreducible)
    (a : Embedding A (RelStructure.Attachment.attach B S D f))
    (hNotCore :
      ¬ copyCarrier a ⊆
        copyCarrier (RelStructure.Attachment.coreEmbedding B S D f)) :
    ∃! i : I,
      copyCarrier a ⊆
        copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) := by
  classical
  let T := copyCarrier a
  have hT : (RelStructure.Attachment.attach B S D f).induce T
      |>.Irreducible :=
    hA.range_embedding a
  rcases RelStructure.Attachment.irreducible_core_or_copy
      (B := B) (S := S) (D := D) (f := f) T hT with
    hCore | ⟨i, hi⟩
  · exfalso
    apply hNotCore
    intro x hx
    let y : T := ⟨x, hx⟩
    obtain ⟨z, hz⟩ := hCore y
    exact ⟨z, hz.symm⟩
  · have hOwner :
        copyCarrier a ⊆
          copyCarrier (RelStructure.Attachment.copyEmbedding B S D f i) := by
      intro x hx
      let y : T := ⟨x, hx⟩
      obtain ⟨z, hz⟩ := hi y
      exact ⟨z, hz.symm⟩
    refine ⟨i, hOwner, ?_⟩
    intro j hj
    exact attachment_unique_standard_owner_off_core
      B S D f T hNotCore hOwner hj

end StructuralRamsey.Girth
