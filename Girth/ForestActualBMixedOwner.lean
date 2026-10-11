import Girth.ForestNoCoreBFromTwoEdges
import Girth.DesignatedBCopyTransportExact
import Girth.ForestActualBCompleteOwnerBoundary
import Girth.ForestMixedIrreducibleCoverage

/-!
# Actual B-copy support ownership WITHOUT local A-edge coverage

The earlier actual B-copy transport in circulation assumed all
local irreducibles were contained in an A-edge lying in some
designated local gluing copy. This is not available in the
nonpruning q>2 recursive witness.

For a genuinely multi-A-edge irreducible B, the core has NO B-copy:
the high-girth decorated local core extends all irreducibles to A,
and two distinct A-copy carriers in B preclude B embedding into A.
Hence every attached B lies in a full standard picture.  Factor it
through that standard embedding, use OLD designated B-coverage
to find an old designated B-copy with the SAME carrier, and transport
its complete A-support exactly. The checked actual projected B-copy
boundary applies to that standard copy.

The OLD picture needs only mixed designated-B-or-A irreducible
coverage, not coverage of every irreducible by B. An old actual
irreducible B-copy must use the designated B alternative, since
B cannot embed into A. No local edge-coverage normalization or
fictional B owner for uncovered core A-edges is introduced.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Actual B-copies have an exact old tested owner and complete
core boundary under the WEAK local irreducible-to-A extension
hypothesis, even with uncovered ambient local A-edges. -/
theorem actualBCopy_testedOwner_and_completeBoundary_fromMixedCover
    (A : RelStructure L UA) [Finite UA]
    (B : RelStructure L VB) (hB : B.Irreducible)
    [Finite VB]
    (a₁ a₂ : RelStructure.Embedding A B)
    (hDifferent : ¬ SameCopy a₁ a₂)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hExtend : RelStructure.IrreduciblesExtendTo A E.toRelStructure)
    (hOld : DesignatedBorACoversIrreducibles A B D C family)
    (hBaseStrong : ∀ b : RelStructure.Embedding B D,
      b ∈ family → AStrong A D (copyCarrier b))
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
  let fRel : I → RelStructure.Embedding
      (C.toRelStructure.induce S) E.toRelStructure :=
    fun i => (f i).toEmbedding
  obtain ⟨i, hStd⟩ :=
    attached_bCopy_standard_of_multiACopyB
      A B hB a₁ a₂ hDifferent C.toRelStructure S E.toRelStructure
      fRel hExtend bNew
  let std : RelStructure.Embedding C.toRelStructure
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let bOld : RelStructure.Embedding B C.toRelStructure :=
    bNew.factorThroughRange std hStd
  have hNewFactor : bNew = std.comp bOld := by
    apply RelStructure.Embedding.ext
    intro u
    exact (Classical.choose_spec (hStd u)).symm
  obtain ⟨q, hSame⟩ :=
    actualBCopy_designated_of_mixedCoverage
      A B hB D C family hOld
      (noEmbeddingBA_of_two_distinct_ACopies A B a₁ a₂ hDifferent)
      bOld
  have hOldPieceEq :
      bSupportPiece A bOld = bSupportPiece A q.embedding :=
    bSupportPiece_eq_of_sameCopy A bOld q.embedding hSame
  have hNewPieceEq :
      bSupportPiece A bNew =
        bSupportPiece A (std.comp q.embedding) := by
    calc
      bSupportPiece A bNew =
        bSupportPiece A (std.comp bOld) :=
          congrArg (bSupportPiece A) hNewFactor
      _ = (bSupportPiece A bOld).map std.toFunctionEmbedding :=
        (bSupportPiece_map_exact A bOld std).symm
      _ = (bSupportPiece A q.embedding).map std.toFunctionEmbedding :=
        congrArg (fun U : HypergraphPiece X =>
          U.map std.toFunctionEmbedding) hOldPieceEq
      _ = bSupportPiece A (std.comp q.embedding) :=
        bSupportPiece_map_exact A q.embedding std
  have hTest : TransportedPiece testedOld
      std.toFunctionEmbedding (bSupportPiece A bNew) := by
    rw [hNewFactor]
    refine ⟨bSupportPiece A bOld, ?_, ?_⟩
    · rw [hOldPieceEq]
      exact hTestOld q
    · exact (bSupportPiece_map_exact A bOld std).symm
  have hBoundary : SmallOrWholeEdgeBoundary
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier (core.comp aE)}
      (copyCarrier core)
      (bSupportPiece A bNew) := by
    rw [hNewPieceEq]
    exact attachedProjectedBCopy_completeSupportBoundary
      A B D C e q.base q.lift
      (hBaseStrong q.base q.base_mem) E f i
  exact ⟨i, hTest, hBoundary⟩

end StructuralRamsey.Girth
