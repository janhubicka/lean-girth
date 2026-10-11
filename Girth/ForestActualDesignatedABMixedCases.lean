import Girth.ForestActualACopyTestedBoundary
import Girth.ForestCompleteBSupportIntrinsic
import Girth.ForestDesignatedBSupportTransport
import Girth.DesignatedAttachment

/-!
# Actual designated B-support ownership WITHOUT local A-edge coverage

The recursive forest assertion FF_t quantifies only over genuine
DESIGNATED target copies and ambient A-edges, not over every ambient
B-embedding. The designated B-copies of a picture step are produced
by transporting old designated copies into standard pictures.

Therefore their exact old B-support preimage is definitional:
bSupportPiece commutes with the standard relational embedding.
The required small-or-whole core boundary follows from the old
base A-strongness of those designated copies. Neither conclusion
needs local core A-edges to lie in designated gluing copies, or
even local core irreducibles to extend to a gluing copy.

For the A-edge members, irreducibility, genuine partiteness and
base A-linearity give the already checked core-or-standard dichotomy.
Combining them gives the complete selected support classification
consumed by the conditional direct forest increment without ANY
local designated-edge coverage assumption. This allows a simpler
Part II train proof, while Part I retains its stronger covered
structural local witness and designated-B irreducible invariant.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Every designated B-copy TRANSPORTED by the actual picture-step
construction has a tested old support preimage and its exact complete
local core boundary, without old irreducible-B coverage or local
irreducible-to-designated-gluing-copy coverage hypotheses. -/
theorem transportedDesignatedB_testedOwner_and_boundary
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (q : DesignatedCopy B D C family)
    (hStrong : AStrong A D (copyCarrier q.base))
    (testedOld : HypergraphPiece X → Prop)
    (hTest : testedOld (bSupportPiece A q.embedding))
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let std :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    let bNew := (q.transportToStandard f i).embedding
    TransportedPiece testedOld
      (std.toFunctionEmbedding)
      (bSupportPiece A bNew) ∧
    SmallOrWholeEdgeBoundary
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier (core.comp aE)}
      (copyCarrier core)
      (bSupportPiece A bNew) := by
  let S := activeCarrier A C e.toFunctionEmbedding
  let std :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let bNew := (q.transportToStandard f i).embedding
  constructor
  · exact designated_bSupportPiece_transported
      A std q.embedding testedOld hTest
  · exact attachedProjectedBCopy_completeSupportBoundary
      A B D C e q.base q.lift hStrong E f i

/-- A selected support piece in the ACTUAL partite picture is either
an ambient A-edge or one of the prescribed transported designated
B-copies. Its old-test/exceptional-edge classification follows with
NO local core A-edge coverage by the gluing family. -/
theorem actualDesignatedAB_piece_canonicalOwnerCases
    (A : RelStructure L UA) (hA : A.Irreducible)
    [Finite UA]
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family,
      AStrong A D (copyCarrier q.base))
    (testedOld : HypergraphPiece X → Prop)
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestB : ∀ q : DesignatedCopy B D C family,
      testedOld (bSupportPiece A q.embedding))
    (T : HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding)
        (W := Y) (I := I)))
    (hSelected :
      (∃ aNew : RelStructure.Embedding A
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        T = HypergraphPiece.oneEdge (copyCarrier aNew)) ∨
      (∃ i : I, ∃ q : DesignatedCopy B D C family,
        T = bSupportPiece A (q.transportToStandard f i).embedding)) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    let K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex S
        (W := Y) (I := I))) :=
      {t | ∃ aE : RelStructure.Embedding A E.toRelStructure,
        t = copyCarrier (core.comp aE)}
    (∃ i : I,
      TransportedPiece testedOld
        ((StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding)
        T ∧ SmallOrWholeEdgeBoundary K (copyCarrier core) T) ∨
    (∃ ce : {ce : Set (StructuralRamsey.Partite.Attachment.Vertex S
        (W := Y) (I := I)) // ce ∈ K},
      T = HypergraphPiece.oneEdge ce.1) := by
  classical
  rcases hSelected with ⟨aNew, hT⟩ | ⟨i, q, hT⟩
  · rcases attached_actualACopy_coreOr_testedStandardBoundary
      A hA D C hPartite hLinear e E f testedOld hTestA aNew with
      hCore | ⟨i, hTest, hBoundary⟩
    · exact Or.inr ⟨⟨copyCarrier aNew, hCore⟩, hT⟩
    · left
      refine ⟨i, ?_, ?_⟩
      · rw [hT]
        exact hTest
      · rw [hT]
        exact hBoundary
  · obtain ⟨hTest, hBoundary⟩ :=
      transportedDesignatedB_testedOwner_and_boundary
        A B D C family e E f q (hBaseStrong q)
        testedOld (hTestB q) i
    left
    refine ⟨i, ?_, ?_⟩
    · rw [hT]
      exact hTest
    · rw [hT]
      exact hBoundary

/-- Finite families inherit the identical canonical mixed-owner
certificate, with no assumptions about arbitrary ambient B-copies
and no local irreducible-to-gluing coverage. -/
theorem actualDesignatedAB_family_canonicalOwnerCases
    (A : RelStructure L UA) (hA : A.Irreducible)
    [Finite UA]
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family,
      AStrong A D (copyCarrier q.base))
    (testedOld : HypergraphPiece X → Prop)
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestB : ∀ q : DesignatedCopy B D C family,
      testedOld (bSupportPiece A q.embedding))
    {N : Type v}
    (selected : N → HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding)
        (W := Y) (I := I)))
    (hSelected : ∀ n : N,
      (∃ aNew : RelStructure.Embedding A
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        selected n = HypergraphPiece.oneEdge (copyCarrier aNew)) ∨
      (∃ i : I, ∃ q : DesignatedCopy B D C family,
        selected n =
          bSupportPiece A (q.transportToStandard f i).embedding)) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    let K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex S
        (W := Y) (I := I))) :=
      {t | ∃ aE : RelStructure.Embedding A E.toRelStructure,
        t = copyCarrier (core.comp aE)}
    ∀ n : N,
      (∃ i : I, TransportedPiece testedOld
        ((StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding)
        (selected n) ∧
        SmallOrWholeEdgeBoundary K (copyCarrier core) (selected n)) ∨
      (∃ ce : {ce : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) // ce ∈ K},
        selected n = HypergraphPiece.oneEdge ce.1) := by
  intro S core K n
  exact actualDesignatedAB_piece_canonicalOwnerCases
    A hA B D C hPartite hLinear family e E f
    hBaseStrong testedOld hTestA hTestB (selected n) (hSelected n)

end StructuralRamsey.Girth
