import Girth.DesignatedBCopyTransportExact
import Girth.ForestDesignatedBSupportTransport

/-!
# Every actual attached B-copy has an exact old tested standard owner

The circulation mixed-owner direct forest increment needs each
selected genuine B-copy to be a *tested* support piece inside a
full standard picture. Merely assigning its carrier to a standard
picture is insufficient: the complete family of A-support edges
must be transported exactly.

The designated coverage theorem classifies any actual B-copy by
one transported old designated copy, with equal full A-support.
Exact support transport under the standard embedding then gives
the tested old support-piece preimage required for the forest
increment.

This theorem uses the genuine structural local witness coverage
and old designated irreducible coverage. It does not assume that
all ambient edges of a recursively built train witness belong to
designated gluing copies.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- The complete A-support of every ambient B-copy in the
genuine partite attachment is a canonical image of an old tested
designated B-support piece. -/
theorem actualBCopy_has_tested_standard_owner
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (hB : B.Irreducible)
    [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : DesignatedCoversIrreducibles B D C family)
    (hLocal : LocalIrreduciblesCoveredByAInCopies A E f)
    (testedOld : HypergraphPiece X → Prop)
    (hTest : ∀ q : DesignatedCopy B D C family,
      testedOld (bSupportPiece A q.embedding))
    (bNew : RelStructure.Embedding B
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure) :
    ∃ i : I,
      TransportedPiece testedOld
        (relationEmbeddingToFunction
          (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding)
        (bSupportPiece A bNew) := by
  classical
  obtain ⟨i, q, _hSame, hSupportEq⟩ :=
    actualBCopy_is_transported_designated
      A hA B hB D C family S E f hOld hLocal bNew
  let std : RelStructure.Embedding C.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  have hTransport :
      (q.transportToStandard f i).embedding =
        std.comp q.embedding := by
    rfl
  have hOwned :
      TransportedPiece testedOld
        (relationEmbeddingToFunction std)
        (bSupportPiece A (std.comp q.embedding)) :=
    designated_bSupportPiece_transported
      A std q.embedding testedOld (hTest q)
  refine ⟨i, ?_⟩
  rw [hSupportEq, hTransport]
  exact hOwned

end StructuralRamsey.Girth
