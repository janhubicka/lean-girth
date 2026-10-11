import Girth.ForestActualACopyMixedOwner
import Girth.ForestActualPartiteBoundary
import Girth.ForestActualACopyOneEdge
import Girth.ActiveCarrierStrong

/-!
# Actual attached A-copy: physical core edge OR tested standard A-copy with boundary

This is the A-side companion of the genuine B-copy owner/boundary
bridge in the circulation forest increment.

We do NOT require local core edges to belong to designated gluing
B-copies.  Irreducibility splits every actual A-copy into one lying
entirely in the new core, or one lying in a full standard picture.

* In the core, it is itself an actual local core A-support edge and
  therefore owns itself as a one-edge mixed owner.
* In a standard picture, it factors through an old A-embedding with
  an exact old tested one-edge preimage.  The genuine D-partite
  projection of the old picture maps that embedding to an actual
  base A-embedding.  Base A-linearity and the checked projected
  A-copy boundary lemma give a subsingleton/whole-edge boundary.
  Finite A identifies the COMPLETE self A-support with the formal
  one-edge selected support member.

The statement uses only honest D-partiteness and A-linearity in
addition to the free relational attachment and old A-edge testing.
It does not use the recursive edge-coverage pruning operation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Every actual A-copy of a partite attachment is a genuine core
support edge, or a transported OLD TESTED A-edge in one full
standard picture with its exact small-or-whole core boundary. -/
theorem attached_actualACopy_coreOr_testedStandardBoundary
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    [Finite UA]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (testedOld : HypergraphPiece X → Prop)
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (aNew : RelStructure.Embedding A
      (StructuralRamsey.Partite.Attachment.attach C
        (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    let K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex S
        (W := Y) (I := I))) :=
      {t | ∃ aE : RelStructure.Embedding A E.toRelStructure,
        t = copyCarrier (core.comp aE)}
    (copyCarrier aNew ∈ K) ∨
      (∃ i : I,
        TransportedPiece testedOld
          ((StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding)
          (HypergraphPiece.oneEdge (copyCarrier aNew)) ∧
        SmallOrWholeEdgeBoundary K (copyCarrier core)
          (HypergraphPiece.oneEdge (copyCarrier aNew))) := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex S
      (W := Y) (I := I))) :=
    {t | ∃ aE : RelStructure.Embedding A E.toRelStructure,
      t = copyCarrier (core.comp aE)}
  let fRel : I → RelStructure.Embedding
      (C.toRelStructure.induce S) E.toRelStructure :=
    fun i => (f i).toEmbedding
  rcases attachment_aCopy_core_or_standard
      A hA C.toRelStructure S E.toRelStructure fRel aNew with
    hCore | ⟨i, hStandard⟩
  · left
    have hInside : copyCarrier aNew ⊆ copyCarrier core := by
      rintro z ⟨u, rfl⟩
      obtain ⟨y, hy⟩ := hCore u
      exact ⟨y, hy.symm⟩
    exact embeddedACopy_mem_mappedCoreSupport A core aNew hInside
  · right
    let std : RelStructure.Embedding C.toRelStructure
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let aOld : RelStructure.Embedding A C.toRelStructure :=
      aNew.factorThroughRange std hStandard
    have hFactor (u : UA) : aNew u = std (aOld u) :=
      Classical.choose_spec (hStandard u)
    obtain ⟨b, hb⟩ :=
      hPartite.after_irreducible_embedding hA aOld
    let q : StructuralRamsey.Partite.ProjectedEmbedding A C b :=
      ⟨aOld, hb⟩
    have hEquals : std.comp q.val = aNew := by
      apply RelStructure.Embedding.ext
      intro u
      exact (hFactor u).symm
    have hBoundaryStd :
        SmallOrWholeEdgeBoundary K (copyCarrier core)
          (embeddedACopySupportPiece A (std.comp q.val)) :=
      attachedProjectedACopy_smallOrWholeBoundary
        A D C e b q hLinear E f i
    have hOneEdge :
        embeddedACopySupportPiece A aNew =
          HypergraphPiece.oneEdge (copyCarrier aNew) :=
      embeddedACopySupportPiece_self_eq_oneEdge A aNew
    rw [hEquals, hOneEdge] at hBoundaryStd
    have hTested :
        TransportedPiece testedOld std.toFunctionEmbedding
          (HypergraphPiece.oneEdge (copyCarrier aNew)) :=
      attached_standard_aCopy_transported
        A C.toRelStructure S E.toRelStructure fRel i
        aNew hStandard testedOld hTestA
    exact ⟨i, hTested, hBoundaryStd⟩

end StructuralRamsey.Girth
