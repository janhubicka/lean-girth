import Girth.ForestCompleteBSupportIntrinsic
import Girth.DesignatedBCopyTransportExact
import Girth.ForestDesignatedBSupportTransport

/-!
# Actual B copies: exact tested owner AND complete local boundary

The abstract mixed-owner forest increment requires both an old tested
support-piece preimage and a small-or-whole local core boundary for
every selected B-support piece in the actual partite attachment.

These requirements follow together from:
* old designated B-copy coverage and local irreducible-to-A coverage;
* finiteness of the target B, giving equality with a transported
  old designated B-copy, not merely carrier inclusion;
* exact transport of COMPLETE ambient A-support pieces;
* A-strongness of each designated base B-copy and the checked
  actual projected B-copy local boundary theorem.

No recursive edge-coverage normalization or assumption that every
local ambient A-edge belongs to a designated gluing B-copy is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Every ambient B-copy in the genuine induced partite attachment
has a standard owner testing its exact complete A-support, and the
same support has the correct whole-edge/vertex core boundary. -/
theorem actualBCopy_testedOwner_and_completeBoundary
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (hB : B.Irreducible)
    [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hOld : DesignatedCoversIrreducibles B D C family)
    (hLocal : LocalIrreduciblesCoveredByAInCopies A E f)
    (hBaseStrong :
      ∀ b : RelStructure.Embedding B D, b ∈ family →
        AStrong A D (copyCarrier b))
    (testedOld : HypergraphPiece X → Prop)
    (hTestOld : ∀ q : DesignatedCopy B D C family,
      testedOld (bSupportPiece A q.embedding))
    (bNew : RelStructure.Embedding B
      (StructuralRamsey.Partite.Attachment.attach C
        (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    ∃ i : I,
      TransportedPiece testedOld
        ((StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding)
        (bSupportPiece A bNew) ∧
      SmallOrWholeEdgeBoundary
        {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
            (W := Y) (I := I)) |
          ∃ aE : RelStructure.Embedding A E.toRelStructure,
            t = copyCarrier (core.comp aE)}
        (copyCarrier core)
        (bSupportPiece A bNew) := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  obtain ⟨i, q, _hSame, hSupport⟩ :=
    actualBCopy_is_transported_designated
      A hA B hB D C family S E f hOld hLocal bNew
  let std : RelStructure.Embedding C.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  have hAsComp :
      (q.transportToStandard f i).embedding =
        std.comp q.embedding := by
    rfl
  have hTestedStd :
      TransportedPiece testedOld
        std.toFunctionEmbedding
        (bSupportPiece A (std.comp q.embedding)) :=
    designated_bSupportPiece_transported
      A std q.embedding testedOld (hTestOld q)
  have hBoundaryStd :
      SmallOrWholeEdgeBoundary
        {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
            (W := Y) (I := I)) |
          ∃ aE : RelStructure.Embedding A E.toRelStructure,
            t = copyCarrier (core.comp aE)}
        (copyCarrier core)
        (bSupportPiece A (std.comp q.embedding)) :=
    attachedProjectedBCopy_completeSupportBoundary
      A B D C e q.base q.lift
      (hBaseStrong q.base q.base_mem) E f i
  refine ⟨i, ?_, ?_⟩
  · rw [hSupport, hAsComp]
    exact hTestedStd
  · rw [hSupport, hAsComp]
    exact hBoundaryStd

end StructuralRamsey.Girth
