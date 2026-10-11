import Girth.ForestNoCoreBCopy

/-!
# A target containing two distinct A-support carriers cannot embed in A

The nontrivial q>2 local gluing target P has at least two distinct
actual A-copies. Since A is finite, any embedding A -> A is
surjective. If P embedded in A then either of its A-copies would
have to cover ALL of P. Hence their carriers would coincide, a
contradiction.

This derives the crucial no-B-into-A hypothesis of the noncoverage
local B-copy standard-owner theorem from the exact nontrivial
multi-A-edge condition used by the manuscript. No vertex-count
arithmetic or rigidity of the source A is required.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB : Type v}

/-- Two different physical embedded A-carriers in B prevent
an embedding B -> A, for finite A. -/
theorem noEmbeddingBA_of_two_distinct_ACopies
    (A : RelStructure L UA) [Finite UA]
    (B : RelStructure L VB)
    (a₁ a₂ : RelStructure.Embedding A B)
    (hDifferent : ¬ SameCopy a₁ a₂) :
    ¬ Nonempty (RelStructure.Embedding B A) := by
  rintro ⟨b⟩
  have hSurj₁ : Function.Surjective (b.comp a₁) :=
    Finite.injective_iff_surjective.mp (b.comp a₁).injective
  have hSurj₂ : Function.Surjective (b.comp a₂) :=
    Finite.injective_iff_surjective.mp (b.comp a₂).injective
  have hA₁ : Function.Surjective a₁ := by
    intro y
    obtain ⟨x, hx⟩ := hSurj₁ (b y)
    refine ⟨x, ?_⟩
    apply b.injective
    exact hx
  have hA₂ : Function.Surjective a₂ := by
    intro y
    obtain ⟨x, hx⟩ := hSurj₂ (b y)
    refine ⟨x, ?_⟩
    apply b.injective
    exact hx
  apply hDifferent
  change Set.range a₁ = Set.range a₂
  ext y
  constructor
  · intro _
    obtain ⟨x, hx⟩ := hA₂ y
    exact ⟨x, hx⟩
  · intro _
    obtain ⟨x, hx⟩ := hA₁ y
    exact ⟨x, hx⟩

/-- For an irreducible nontrivial B-target with at least two
distinct A-support carriers, irreducible-to-A extension in the local
core guarantees every attached B-copy lies in a standard picture. -/
theorem attached_bCopy_standard_of_multiACopyB
    (A : RelStructure L UA) [Finite UA]
    (B : RelStructure L VB) (hB : B.Irreducible)
    (a₁ a₂ : RelStructure.Embedding A B)
    (hDifferent : ¬ SameCopy a₁ a₂)
    {Old Core I : Type v}
    (OldPicture : RelStructure L Old)
    (S : Set Old)
    (E : RelStructure L Core)
    (f : I → RelStructure.Embedding (OldPicture.induce S) E)
    (hExtend : RelStructure.IrreduciblesExtendTo A E)
    (b : RelStructure.Embedding B
      (RelStructure.Attachment.attach OldPicture S E f)) :
    ∃ i : I, ∀ u : VB, ∃ x : Old,
      b u = (RelStructure.Attachment.copyEmbedding
        OldPicture S E f i) x := by
  exact attached_bCopy_standard_of_noCoreB
    A B hB OldPicture S E f hExtend
      (noEmbeddingBA_of_two_distinct_ACopies A B a₁ a₂ hDifferent) b

end StructuralRamsey.Girth
