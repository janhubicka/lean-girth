import Girth.DesignatedAttachment
import Girth.AttachmentGeometry

/-! # Shared support through a picture attachment

This module isolates the nontrivial cross-copy mechanism in the manuscript's
shared-support preservation argument.  A point where a transported designated
B-copy meets the new core comes from an old active vertex.  The old
B-versus-A shared-support property then gives a supporting A-copy inside the
transported B-copy.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- A vertex of a designated B-copy is supported inside that copy by an
A-copy. -/
def VertexSupportedInDesignated
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L P}
    {C : StructuralRamsey.Partite.System L P X}
    {family : Set (RelStructure.Embedding B D)}
    (q : DesignatedCopy B D C family)
    (x : X) : Prop :=
  ∃ a : RelStructure.Embedding A B,
    x ∈ copyCarrier (q.embedding.comp a)

/-- Old shared-support property between designated B-copies and ambient
A-copies.  The A-copy itself supplies support on its side; the predicate asks
only for support inside the incident B-copy. -/
def DesignatedSupportsACopies
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L P}
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) : Prop :=
  ∀ (q : DesignatedCopy B D C family)
    (a : RelStructure.Embedding A C.toRelStructure)
    (x : X),
    x ∈ copyCarrier q.embedding →
    x ∈ copyCarrier a →
    VertexSupportedInDesignated A q x

/-- A point of a transported designated copy that lies in the attachment core
comes from an old active vertex and is supported inside the transported copy. -/
theorem transportedDesignated_corePoint_supported
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (hShared : DesignatedSupportsACopies A C family)
    (i : I)
    (q : DesignatedCopy B D C family)
    (z : StructuralRamsey.Partite.Attachment.Vertex
      (activeCarrier A C α) (W := Y) (I := I))
    (hzCopy :
      z ∈ copyCarrier
        (q.transportToStandard f i).embedding)
    (hzCore :
      z ∈ copyCarrier
        (StructuralRamsey.Partite.Attachment.coreEmbedding
          C (activeCarrier A C α) E f).toEmbedding) :
    ∃ a : RelStructure.Embedding A B,
      z ∈ copyCarrier
        ((q.transportToStandard f i).embedding.comp a) := by
  classical
  let S := activeCarrier A C α
  let copyE :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let coreE :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  rcases hzCopy with ⟨b, hb⟩
  rcases hzCore with ⟨y, hy⟩
  have hEq :
      copyE (q.embedding b) = coreE y :=
    hb.trans hy.symm
  have hOldInS : q.embedding b ∈ S := by
    change
      RelStructure.Attachment.copyMap
          C.toRelStructure S E.toRelStructure
          (fun k => (f k).toEmbedding) i (q.embedding b) =
        Sum.inl y at hEq
    exact RelStructure.Attachment.mem_of_copyMap_eq_inl hEq
  rcases hOldInS with ⟨aOld, u, hu⟩
  have hOldInQ :
      q.embedding b ∈ copyCarrier q.embedding :=
    ⟨b, rfl⟩
  have hOldInA :
      q.embedding b ∈ copyCarrier aOld.val := by
    exact ⟨u, hu.symm⟩
  obtain ⟨aB, haB⟩ :=
    hShared q aOld.val (q.embedding b) hOldInQ hOldInA
  refine ⟨aB, ?_⟩
  rcases haB with ⟨u0, hu0⟩
  refine ⟨u0, ?_⟩
  change copyE (q.embedding (aB u0)) = z
  calc
    copyE (q.embedding (aB u0)) =
        copyE (q.embedding b) := congrArg copyE hu0
    _ = z := hb

end StructuralRamsey.Girth
