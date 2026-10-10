import Girth.DesignatedBCopyTransportExact
import Girth.ForestDesignatedBSupportTransport
import Girth.ForestRelationalABCompletion

/-!
# Actual B-copy supports are designated transported supports

The circulation forest-completion invariant tests actual ambient
A-support edges and designated transported B-supports. Subsequent
applications also consider arbitrary ambient B-copies. Irreducible
coverage and finiteness identify each such B-copy with an indexed
transport of a genuine old designated B-copy.

The equality is of the complete A-support HypergraphPiece, not merely
its B-carrier. This module expresses the result in the very same
attachedDesignatedSupport predicate used by forest completion.

The local-forest Ramsey witness and global induction remain separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Supports of genuine old designated B-copies with the prescribed
base projection in a partite picture. -/
def oldDesignatedBCopySupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (T : HypergraphPiece X) : Prop :=
  ∃ q : DesignatedCopy B D C family,
    T = bSupportPiece A q.embedding

/-- Every actual new B-copy's complete A-support is the image of
an old designated B-support through the real standard embedding. -/
theorem actualBCopy_support_exact_standard_image
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
    (bNew : RelStructure.Embedding B
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure) :
    ∃ (i : I) (q : DesignatedCopy B D C family),
      bSupportPiece A bNew =
        (bSupportPiece A q.embedding).map
          (relationEmbeddingToFunction
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C S E f i).toEmbedding) := by
  obtain ⟨i, q, _hSame, hSupport⟩ :=
    actualBCopy_is_transported_designated
      A hA B hB D C family S E f hOld hLocal bNew
  refine ⟨i, q, ?_⟩
  calc
    bSupportPiece A bNew =
        bSupportPiece A ((q.transportToStandard f i).embedding) :=
      hSupport
    _ = (bSupportPiece A q.embedding).map
          (relationEmbeddingToFunction
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C S E f i).toEmbedding) := by
      exact (bSupportPiece_map_exact A q.embedding
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          C S E f i).toEmbedding).symm

/-- ALL ambient B-support pieces satisfy the exact designated-support
predicate consumed by the quantified forest-completion theorem. -/
theorem actualBCopy_mem_attachedDesignatedSupport
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
    (bNew : RelStructure.Embedding B
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure) :
    attachedDesignatedSupport
      C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding)
      (oldDesignatedBCopySupport A B D C family)
      (bSupportPiece A bNew) := by
  obtain ⟨i, q, hExact⟩ :=
    actualBCopy_support_exact_standard_image
      A hA B hB D C family S E f hOld hLocal bNew
  exact ⟨i, bSupportPiece A q.embedding, ⟨q, rfl⟩, hExact⟩

end StructuralRamsey.Girth
