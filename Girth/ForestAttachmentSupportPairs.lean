import Girth.AttachmentGeometry
import Girth.ForestImage

/-!
# Exact small/full support intersections in a free picture attachment

The circulation forest completion uses two different carrier families:
the full images of old standard pictures and the smaller gluing images of
their active subsystem. For different standard-picture labels, their
pairwise intersections agree exactly.

This file derives the support-piece version of this fact from the
already formalized relational attachment geometry. A full old support
piece has the ENTIRE old vertex set as its carrier. A small local
support piece is required to have the actual core image of the
corresponding gluing copy as its carrier, as ensured for decorated
strong-support copies by the local-forest support-piece interface.

This eliminates an independent pair-intersection assumption at the
set-theoretic attachment step. Constructing the needed local strong
support copies and their owned A/B pieces remains a separate task.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W I : Type v}

/-- Forget relational reflection, retaining an injective map of vertex
sets. We need this for the hypergraph-piece image constructor. -/
def relationEmbeddingToFunction
    {A : RelStructure L V} {D : RelStructure L W}
    (e : RelStructure.Embedding A D) : V ↪ W where
  toFun := e.toFun
  inj' := e.injective

@[simp] theorem relationEmbeddingToFunction_apply
    {A : RelStructure L V} {D : RelStructure L W}
    (e : RelStructure.Embedding A D) (x : V) :
    relationEmbeddingToFunction e x = e x := rfl

/-- A full standard picture is an image of a whole old picture.
Consequently its support-piece carrier is the carrier of the
corresponding attached relational standard copy. -/
theorem attachment_full_supportPiece_carrier
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldFull : HypergraphPiece V)
    (hFull : oldFull.carrier = Set.univ)
    (i : I) :
    (oldFull.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))).carrier =
      copyCarrier
        (RelStructure.Attachment.copyEmbedding B S D f i) := by
  change (relationEmbeddingToFunction
      (RelStructure.Attachment.copyEmbedding B S D f i)) ''
        oldFull.carrier =
    Set.range (RelStructure.Attachment.copyEmbedding B S D f i)
  rw [hFull]
  apply Set.ext
  intro z
  constructor
  · rintro ⟨x, _hx, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Set.mem_univ _, hx⟩

/-- The exact pairwise intersection needed to transport the local forest
join tree to the full standard pictures. The only local hypothesis says
that each small gluing support piece uses precisely the true core
image of its local gluing copy. -/
theorem attachment_full_small_support_pair_eq
    (B : RelStructure L V) (S : Set V) (D : RelStructure L W)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldFull : HypergraphPiece V)
    (hFull : oldFull.carrier = Set.univ)
    (small : I →
      HypergraphPiece
        (RelStructure.Attachment.Vertex S (W := W) (I := I)))
    (hSmall :
      ∀ i : I,
        (small i).carrier =
          copyCarrier
            ((RelStructure.Attachment.coreEmbedding B S D f).comp (f i))) :
    ∀ ⦃i j : I⦄, i ≠ j →
      (oldFull.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f i))).carrier ∩
      (oldFull.map (relationEmbeddingToFunction
        (RelStructure.Attachment.copyEmbedding B S D f j))).carrier =
      (small i).carrier ∩ (small j).carrier := by
  intro i j hij
  rw [attachment_full_supportPiece_carrier B S D f oldFull hFull i,
    attachment_full_supportPiece_carrier B S D f oldFull hFull j,
    hSmall i, hSmall j]
  exact attachment_copy_copy_intersection B S D f hij

end StructuralRamsey.Girth
