import Girth.ForestAttachmentSupportPairs

/-!
# Exact two-carrier geometry in a genuine free partite picture

The direct forest increment uses TWO support carriers for every
standard picture: its small local gluing support and its full image of
the old picture. Their intersections must not be conflated.

The actual relational free attachment supplies all three required
identities at once, provided the small support piece is exactly the
image of the local gluing copy and the old full piece has carrier
Set.univ:
  * full carrier = image of the entire standard embedding;
  * full carrier ∩ core carrier = small gluing carrier;
  * intersections of distinct full carriers = intersections of
    their small gluing carriers.

This eliminates separately stated full/core and inter-standard
intersection hypotheses from the concrete forest proof. It does
not assume that private full-picture vertices lie on support edges.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {Old Core I : Type v}

/-- Package every carrier-intersection identity required by the
conditional mixed-owner forest increment, using actual ATTACHMENT
geometry rather than an abstract two-carrier interface. -/
theorem actualAttachment_fullSmallCarrierGeometry
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldFull : HypergraphPiece Old)
    (hFull : oldFull.carrier = Set.univ)
    (small : I → HypergraphPiece
      (RelStructure.Attachment.Vertex S (W := Core) (I := I)))
    (hSmall : ∀ i : I,
      (small i).carrier =
        copyCarrier
          ((RelStructure.Attachment.coreEmbedding B S D f).comp (f i))) :
    let full : I → HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
      fun i => oldFull.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))
    let core := RelStructure.Attachment.coreEmbedding B S D f
    (∀ i : I, (full i).carrier =
      Set.range (RelStructure.Attachment.copyEmbedding B S D f i)) ∧
    (∀ i : I,
      (full i).carrier ∩ copyCarrier core =
        (small i).carrier) ∧
    (∀ ⦃i j : I⦄, i ≠ j →
      (full i).carrier ∩ (full j).carrier =
        (small i).carrier ∩ (small j).carrier) := by
  let full : I → HypergraphPiece
      (RelStructure.Attachment.Vertex S (W := Core) (I := I)) :=
    fun i => oldFull.map (relationEmbeddingToFunction
      (RelStructure.Attachment.copyEmbedding B S D f i))
  let core := RelStructure.Attachment.coreEmbedding B S D f
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact attachment_full_supportPiece_carrier
      B S D f oldFull hFull i
  · intro i
    change
      (oldFull.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))).carrier ∩
      copyCarrier core = (small i).carrier
    rw [attachment_full_supportPiece_carrier B S D f oldFull hFull i,
      hSmall i]
    exact attachment_copy_core_intersection B S D f i
  · intro i j hij
    exact attachment_full_small_support_pair_eq
      B S D f oldFull hFull small hSmall hij

end StructuralRamsey.Girth
