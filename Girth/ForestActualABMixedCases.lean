import Girth.ForestActualACopyTestedBoundary
import Girth.ForestActualBCompleteOwnerBoundary
import Girth.ForestCanonicalMixedOwnerCases

/-!
# Actual A/B selected pieces have the exact physical mixed-owner certificate

The direct mixed-owner increment was already checked for an ABSTRACT
finite family satisfying a regular/exceptional owner certificate.
This file derives the pointwise certificate from the actual relational
partite attachment. A selected support piece is by hypothesis a
genuine ambient A-edge or the complete A-support of a genuine ambient
B-copy; those are exactly the two kinds used by the manuscript.

An actual A-copy in the local core owns its physical A-edge. A standard
A-copy has an exact old tested A-edge and the precise local-core boundary.
Every actual B-copy has an exact old tested COMPLETE B-support preimage
and the precise boundary. Thus the owner classifier uses no spurious
edge-coverage assumption on the recursive train witness, and does not
pretend duplicate embedding labels are distinct physical pieces.

The remaining *separate* obligations are the genuine local Ramsey
witness, bounded local mixed forests, and the geometric conditions
of the global picture-step increment.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- In the actual free partite attachment, every selected genuine
A/B support piece has either a regular old tested standard owner with
its exact local boundary, or is literally a local core A-edge. -/
theorem actualAB_piece_canonicalOwnerCases
    (A : RelStructure L UA)
    (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB)
    (hB : B.Irreducible) [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
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
      (∃ bNew : RelStructure.Embedding B
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        T = bSupportPiece A bNew)) :
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
  rcases hSelected with ⟨aNew, hT⟩ | ⟨bNew, hT⟩
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
  · obtain ⟨i, hTest, hBoundary⟩ :=
      actualBCopy_testedOwner_and_completeBoundary
        A hA B hB D C family e E f
        hOld hLocal hBaseStrong testedOld hTestB bNew
    left
    refine ⟨i, ?_, ?_⟩
    · rw [hT]
      exact hTest
    · rw [hT]
      exact hBoundary

/-- The genuine pointwise classification automatically provides
the finite-family canonical owner cases consumed by the already
verified mixed-owner selection theorem. No owner function is assumed. -/
theorem actualAB_family_canonicalOwnerCases
    (A : RelStructure L UA)
    (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB)
    (hB : B.Irreducible) [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
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
      (∃ bNew : RelStructure.Embedding B
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        selected n = bSupportPiece A bNew)) :
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
  intro n
  exact actualAB_piece_canonicalOwnerCases
    A hA B hB D C hPartite hLinear family e E f
    hOld hLocal hBaseStrong testedOld hTestA hTestB
    (selected n) (hSelected n)

end StructuralRamsey.Girth
