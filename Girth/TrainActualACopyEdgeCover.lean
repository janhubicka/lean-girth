import Girth.ForestActualACopyOwner

/-!
# Exact A-support edge cover in a genuine free relational picture

The physical A-edges of the attached structure are the image
carriers of REAL embeddings of irreducible A. The checked relational
attachment core-or-standard lemma implies that every such edge
is exactly a core A-support edge or exactly the transported support
of an old A-copy in one standard picture.

The resulting set equality supplies the physical EDGE-COVER premise
needed by the concrete train wagon normal-form approach. It does
not yet identify which standard edges are exactly shared with the
core, nor prove injectivity of the map from a formal edge pushout
onto the set of actual physical A-support carriers.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- All genuine physical A-support edge carriers of a relational
structure, with no choice of designated embeddings. -/
def actualACopyCarriers
    (A : RelStructure L UA) {W : Type v}
    (R : RelStructure L W) : Set (Set W) :=
  {e | ∃ a : RelStructure.Embedding A R, e = copyCarrier a}

/-- Every actual A-support edge of a free relational attachment
is EXACTLY the image of a whole old A-copy or a whole core A-copy.
No uncovered core edge is spuriously assigned to a designated copy. -/
theorem attached_actualACopyCarrier_core_or_standard
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (a : RelStructure.Embedding A
      (RelStructure.Attachment.attach B S D f)) :
    (∃ b : RelStructure.Embedding A D,
      copyCarrier a =
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp b))
    ∨
    (∃ i : I, ∃ b : RelStructure.Embedding A B,
      copyCarrier a =
        copyCarrier
          ((RelStructure.Attachment.copyEmbedding B S D f i).comp b)) := by
  classical
  rcases attachment_aCopy_core_or_standard A hA B S D f a with
    hCore | ⟨i, hOld⟩
  · let core : RelStructure.Embedding D
        (RelStructure.Attachment.attach B S D f) :=
      RelStructure.Attachment.coreEmbedding B S D f
    let b : RelStructure.Embedding A D :=
      a.factorThroughRange core hCore
    have hEq : core.comp b = a := by
      apply RelStructure.Embedding.ext
      intro x
      exact (Classical.choose_spec (hCore x)).symm
    left
    refine ⟨b, ?_⟩
    rw [← hEq]
  · let std : RelStructure.Embedding B
        (RelStructure.Attachment.attach B S D f) :=
      RelStructure.Attachment.copyEmbedding B S D f i
    let b : RelStructure.Embedding A B :=
      a.factorThroughRange std hOld
    have hEq : std.comp b = a := by
      apply RelStructure.Embedding.ext
      intro x
      exact (Classical.choose_spec (hOld x)).symm
    right
    refine ⟨i, b, ?_⟩
    rw [← hEq]

/-- Exact equality of physical support EDGE FAMILIES:
the full attachment's A-support is the union of genuine core
A-copies and transported old standard-picture A-copies.
This is not merely inclusion of their vertex carriers. -/
theorem attached_actualACopyCarriers_eq_core_union_standard
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D) :
    actualACopyCarriers A
      (RelStructure.Attachment.attach B S D f) =
      {e | ∃ b : RelStructure.Embedding A D,
        e = copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp b)}
      ∪
      {e | ∃ i : I, ∃ b : RelStructure.Embedding A B,
        e = copyCarrier
          ((RelStructure.Attachment.copyEmbedding B S D f i).comp b)} := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    rcases attached_actualACopyCarrier_core_or_standard
      A hA B S D f a with ⟨b, hb⟩ | ⟨i, b, hb⟩
    · exact Or.inl ⟨b, hb⟩
    · exact Or.inr ⟨i, b, hb⟩
  · rintro (⟨b, rfl⟩ | ⟨i, b, rfl⟩)
    · exact ⟨(RelStructure.Attachment.coreEmbedding B S D f).comp b, rfl⟩
    · exact ⟨(RelStructure.Attachment.copyEmbedding B S D f i).comp b, rfl⟩

end StructuralRamsey.Girth
