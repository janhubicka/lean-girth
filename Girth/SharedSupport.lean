import Girth.DesignatedAttachment
import Girth.AttachmentGeometry
import PartiteConstruction.Iterated.PureCopyGeometry

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
    exact ⟨u, hu⟩
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


/-- Full B-versus-A shared-support preservation for one transported designated
copy.  An ambient irreducible A-copy is either wholly inside the same standard
copy, where the old shared-support hypothesis applies after pullback, or it
meets that standard copy only through the active support, where the already
verified core-point lemma applies. -/
theorem transportedDesignated_sharedACopy_supported
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (hA : A.Irreducible)
    (hShared : DesignatedSupportsACopies A C family)
    (i : I)
    (q : DesignatedCopy B D C family)
    (a : RelStructure.Embedding A
      (StructuralRamsey.Partite.Attachment.attach
        C (activeCarrier A C α) E f).toRelStructure)
    (z : StructuralRamsey.Partite.Attachment.Vertex
      (activeCarrier A C α) (W := Y) (I := I))
    (hzQ :
      z ∈ copyCarrier
        (q.transportToStandard f i).embedding)
    (hzA : z ∈ copyCarrier a) :
    ∃ aB : RelStructure.Embedding A B,
      z ∈ copyCarrier
        ((q.transportToStandard f i).embedding.comp aB) := by
  classical
  let S := activeCarrier A C α
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let copyE : RelStructure.Embedding C.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let coreE : RelStructure.Embedding E.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  rcases hzQ with ⟨bq, hbq⟩
  rcases hzA with ⟨u, hu⟩
  have hMeet :
      a u = copyE (q.embedding bq) := by
    exact hu.trans hbq.symm
  have hloc :=
    RelStructure.Attachment.irreducible_copy_or_intersection_in_support
      (Control := A) (Base := C.toRelStructure)
      (Core := E.toRelStructure) (S := S)
      (f := fun k => (f k).toEmbedding)
      hA a i
  rcases hloc with hInside | hSupport
  · let aOld : RelStructure.Embedding A C.toRelStructure :=
      a.factorThroughRange copyE hInside
    have haOld (v : UA) : a v = copyE (aOld v) :=
      Classical.choose_spec (hInside v)
    have hOldPoint :
        aOld u = q.embedding bq := by
      apply copyE.injective
      calc
        copyE (aOld u) = a u := (haOld u).symm
        _ = copyE (q.embedding bq) := hMeet
    have hOldInQ :
        q.embedding bq ∈ copyCarrier q.embedding :=
      ⟨bq, rfl⟩
    have hOldInA :
        q.embedding bq ∈ copyCarrier aOld :=
      ⟨u, hOldPoint⟩
    obtain ⟨aB, haB⟩ :=
      hShared q aOld (q.embedding bq) hOldInQ hOldInA
    refine ⟨aB, ?_⟩
    rcases haB with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change copyE (q.embedding (aB v)) = z
    calc
      copyE (q.embedding (aB v)) =
          copyE (q.embedding bq) := congrArg copyE hv
      _ = z := hbq
  · have hqS : q.embedding bq ∈ S := by
      exact hSupport u (q.embedding bq) hMeet
    have hzCore :
        z ∈ copyCarrier coreE := by
      refine ⟨(f i).toEmbedding ⟨q.embedding bq, hqS⟩, ?_⟩
      calc
        coreE ((f i).toEmbedding ⟨q.embedding bq, hqS⟩) =
            copyE (q.embedding bq) := by
          exact
            (StructuralRamsey.Partite.Attachment.copy_extends
              C S E f i ⟨q.embedding bq, hqS⟩).symm
        _ = z := hbq
    exact
      transportedDesignated_corePoint_supported
        A B D C family α E f hShared i q z
        ⟨bq, hbq⟩ hzCore


/-- Old shared-support property between two distinct designated B-copies. -/
def DesignatedSupportsDesignated
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L P}
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) : Prop :=
  ∀ (q r : DesignatedCopy B D C family), q ≠ r →
    ∀ (x : X),
      x ∈ copyCarrier q.embedding →
      x ∈ copyCarrier r.embedding →
      VertexSupportedInDesignated A q x ∧
        VertexSupportedInDesignated A r x

/-- Shared points of two distinct transported designated B-members remain
A-supported in both members.  If the copies lie in the same standard copy,
pull back to the old picture.  If they lie in different standard copies, their
intersection lies in the core and the core-point support lemma applies to both. -/
theorem transportedDesignated_sharedDesignated_supported
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (hSharedA : DesignatedSupportsACopies A C family)
    (hSharedB : DesignatedSupportsDesignated A C family)
    (i j : I)
    (q r : DesignatedCopy B D C family)
    (hDistinct : i ≠ j ∨ q ≠ r)
    (z : StructuralRamsey.Partite.Attachment.Vertex
      (activeCarrier A C α) (W := Y) (I := I))
    (hzQ :
      z ∈ copyCarrier
        (q.transportToStandard f i).embedding)
    (hzR :
      z ∈ copyCarrier
        (r.transportToStandard f j).embedding) :
    (∃ aB : RelStructure.Embedding A B,
      z ∈ copyCarrier
        ((q.transportToStandard f i).embedding.comp aB)) ∧
    (∃ aB : RelStructure.Embedding A B,
      z ∈ copyCarrier
        ((r.transportToStandard f j).embedding.comp aB)) := by
  classical
  let S := activeCarrier A C α
  rcases hzQ with ⟨bq, hbq⟩
  rcases hzR with ⟨br, hbr⟩
  by_cases hij : i = j
  · subst j
    have hqr : q ≠ r := by
      rcases hDistinct with hne | hne
      · exact (hne rfl).elim
      · exact hne
    let copyE : RelStructure.Embedding C.toRelStructure
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    have hOldEq : q.embedding bq = r.embedding br := by
      apply copyE.injective
      exact hbq.trans hbr.symm
    obtain ⟨hqSupp, hrSupp⟩ :=
      hSharedB q r hqr (q.embedding bq)
        ⟨bq, rfl⟩ ⟨br, hOldEq.symm⟩
    constructor
    · rcases hqSupp with ⟨aB, u, hu⟩
      refine ⟨aB, u, ?_⟩
      change copyE (q.embedding (aB u)) = z
      calc
        copyE (q.embedding (aB u)) =
            copyE (q.embedding bq) := congrArg copyE hu
        _ = z := hbq
    · rcases hrSupp with ⟨aB, u, hu⟩
      refine ⟨aB, u, ?_⟩
      change copyE (r.embedding (aB u)) = z
      calc
        copyE (r.embedding (aB u)) =
            copyE (q.embedding bq) := congrArg copyE hu
        _ = z := hbq
  · let copyI : RelStructure.Embedding C.toRelStructure
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let copyJ : RelStructure.Embedding C.toRelStructure
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f j).toEmbedding
    let coreE : RelStructure.Embedding E.toRelStructure
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    have hzI : z ∈ copyCarrier copyI := ⟨q.embedding bq, hbq⟩
    have hzJ : z ∈ copyCarrier copyJ := ⟨r.embedding br, hbr⟩
    have hzCore : z ∈ copyCarrier coreE :=
      attachment_copy_copy_intersection_subset_core
        C.toRelStructure S E.toRelStructure
        (fun k => (f k).toEmbedding) hij ⟨hzI, hzJ⟩
    constructor
    · exact
        transportedDesignated_corePoint_supported
          A B D C family α E f hSharedA i q z
          ⟨bq, hbq⟩ hzCore
    · exact
        transportedDesignated_corePoint_supported
          A B D C family α E f hSharedA j r z
          ⟨br, hbr⟩ hzCore


/-- The two nonvacuous clauses of the manuscript's shared-support invariant:
designated B versus ambient A, and two distinct designated B-members. -/
def DesignatedSharedSupport
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L P}
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) : Prop :=
  DesignatedSupportsACopies A C family ∧
    DesignatedSupportsDesignated A C family

/-- Shared-support invariant for the transported designated family in one
attachment step.  A-A pairs need no clause because there is no incident
B-member to support. -/
def TransportedDesignatedSharedSupport
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L P}
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E) : Prop :=
  (∀ (i : I) (q : DesignatedCopy B D C family)
      (a : RelStructure.Embedding A
        (StructuralRamsey.Partite.Attachment.attach
          C (activeCarrier A C α) E f).toRelStructure)
      (z : StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C α) (W := Y) (I := I)),
      z ∈ copyCarrier (q.transportToStandard f i).embedding →
      z ∈ copyCarrier a →
      ∃ aB : RelStructure.Embedding A B,
        z ∈ copyCarrier
          ((q.transportToStandard f i).embedding.comp aB)) ∧
  (∀ (i j : I) (q r : DesignatedCopy B D C family),
      i ≠ j ∨ q ≠ r →
      ∀ (z : StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C α) (W := Y) (I := I)),
      z ∈ copyCarrier (q.transportToStandard f i).embedding →
      z ∈ copyCarrier (r.transportToStandard f j).embedding →
      (∃ aB : RelStructure.Embedding A B,
        z ∈ copyCarrier
          ((q.transportToStandard f i).embedding.comp aB)) ∧
      (∃ aB : RelStructure.Embedding A B,
        z ∈ copyCarrier
          ((r.transportToStandard f j).embedding.comp aB)))

/-- A standard picture attachment preserves the manuscript's full
shared-support invariant for the transported designated family. -/
theorem transportedDesignated_sharedSupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (hA : A.Irreducible)
    (hShared : DesignatedSharedSupport A C family) :
    TransportedDesignatedSharedSupport
      A C family α E f := by
  constructor
  · intro i q a z hzQ hzA
    exact
      transportedDesignated_sharedACopy_supported
        A B D C family α E f hA hShared.1
        i q a z hzQ hzA
  · intro i j q r hDistinct z hzQ hzR
    exact
      transportedDesignated_sharedDesignated_supported
        A B D C family α E f hShared.1 hShared.2
        i j q r hDistinct z hzQ hzR

end StructuralRamsey.Girth
