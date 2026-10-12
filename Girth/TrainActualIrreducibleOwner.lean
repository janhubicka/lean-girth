import Girth.AttachmentGeometry

/-!
# Actual irreducible support-copy owners in a free picture extension

The physical edge sort in the circulation manuscript consists of
copies of an irreducible support type A. Since a free attachment
creates no mixed relation tuples, every such copy lies completely
in the local core or in ONE actual standard picture. A source
embedding factors through that piece, not just its vertex carrier.

This covers all ambient A-edges, including any uncovered core edge
that belongs to no designated local gluing B-copy. The result is
pure free-attachment geometry, not a local Ramsey theorem or a
certificate of wagon system-Girth.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA V W I : Type v}

/-- Every irreducible copy in a genuine free attachment has a
complete actual embedding into either the core or one standard
picture whose composition gives the ORIGINAL copy. -/
theorem attachment_irreducibleCopy_core_or_standard
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L V) (S : Set V)
    (D : RelStructure L W)
    (f : I → Embedding (B.induce S) D)
    (a : Embedding A (RelStructure.Attachment.attach B S D f)) :
    (∃ b : Embedding A D,
      a = (RelStructure.Attachment.coreEmbedding B S D f).comp b) ∨
    (∃ i : I, ∃ b : Embedding A B,
      a = (RelStructure.Attachment.copyEmbedding B S D f i).comp b) := by
  classical
  let Whole := RelStructure.Attachment.attach B S D f
  let T : Set (RelStructure.Attachment.Vertex S (W := W) (I := I)) :=
    Set.range a
  have hT : (Whole.induce T).Irreducible :=
    hA.range_embedding a
  rcases RelStructure.Attachment.irreducible_core_or_copy
      (B := B) (S := S) (D := D) (f := f) T hT with
    hCore | ⟨i, hCopy⟩
  · let core : Embedding D Whole :=
      RelStructure.Attachment.coreEmbedding B S D f
    have hRange : ∀ x : UA, ∃ y : W, a x = core y := by
      intro x
      obtain ⟨y, hy⟩ := hCore (⟨a x, ⟨x, rfl⟩⟩ : T)
      exact ⟨y, hy⟩
    let b : Embedding A D := a.factorThroughRange core hRange
    refine Or.inl ⟨b, ?_⟩
    apply RelStructure.Embedding.ext
    intro x
    exact Classical.choose_spec (hRange x)
  · let copy : Embedding B Whole :=
      RelStructure.Attachment.copyEmbedding B S D f i
    have hRange : ∀ x : UA, ∃ y : V, a x = copy y := by
      intro x
      obtain ⟨y, hy⟩ := hCopy (⟨a x, ⟨x, rfl⟩⟩ : T)
      exact ⟨y, hy⟩
    let b : Embedding A B := a.factorThroughRange copy hRange
    refine Or.inr ⟨i, b, ?_⟩
    apply RelStructure.Embedding.ext
    intro x
    exact Classical.choose_spec (hRange x)

end StructuralRamsey.Girth
