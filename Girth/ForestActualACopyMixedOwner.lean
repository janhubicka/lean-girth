import Girth.ForestActualACopyOwner
import Girth.ForestCoreFactorBoundary

/-!
# The actual relational A-copy has an owner WITHOUT local edge coverage

The old standard-owner theorem for an attached A-copy required every
core A-copy to lie in a designated local gluing copy.  The direct
mixed-owner forest increment no longer needs this hypothesis.

Irreducibility in the free relational attachment gives an exhaustive
dichotomy: the whole A-copy lies in the local core, or in one full
standard picture. In the core case, its carrier is automatically an
actual A-support edge of the core and thus can OWN ITSELF as a one-edge
mixed owner. In a standard picture, factor through its embedding to
obtain an exact old tested A-copy support preimage.

This is the concrete noncircular A-side of the mixed-owner ownership
classification in the girth circulation draft.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Every genuine A-copy in the attached structure is either an
actual local CORE A-support edge, or the full support image of a
tested old A-copy in a genuine full standard picture.

No gluing-copy COVERAGE assumption appears. -/
theorem attached_aCopy_coreEdge_or_tested_standard
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (testedOld : HypergraphPiece Old → Prop)
    (hTestA :
      ∀ aOld : RelStructure.Embedding A B,
        testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (a : RelStructure.Embedding A
      (RelStructure.Attachment.attach B S D f)) :
    let core := RelStructure.Attachment.coreEmbedding B S D f
    (copyCarrier a ∈
      {e : Set (RelStructure.Attachment.Vertex S (W := Core) (I := I)) |
        ∃ aD : RelStructure.Embedding A D,
          e = copyCarrier (core.comp aD)})
      ∨
    (∃ i : I,
      TransportedPiece testedOld
        (relationEmbeddingToFunction
          (RelStructure.Attachment.copyEmbedding B S D f i))
        (HypergraphPiece.oneEdge (copyCarrier a))) := by
  let core := RelStructure.Attachment.coreEmbedding B S D f
  rcases attachment_aCopy_core_or_standard
      A hA B S D f a with hCore | ⟨i, hStandard⟩
  · left
    have hInside : copyCarrier a ⊆ copyCarrier core := by
      rintro z ⟨u, rfl⟩
      obtain ⟨y, hy⟩ := hCore u
      exact ⟨y, hy.symm⟩
    exact embeddedACopy_mem_mappedCoreSupport A core a hInside
  · right
    exact ⟨i, attached_standard_aCopy_transported
      A B S D f i a hStandard testedOld hTestA⟩

end StructuralRamsey.Girth
