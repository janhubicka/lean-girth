import Girth.ForestActualPartiteDirectIncrement
import Girth.AttachmentGeometry

/-!
# Remove independent pair/core overlap assumptions from the actual forest increment

The finite direct mixed-owner forest theorem for genuine A/B support
pieces must use the geometry of the ACTUAL free attachment. The
intersections of two distinct full standard pictures are exactly those
of their small gluing images; and each standard copy meets the core
exactly along its gluing image. Those are already checked attachment
lemmas, not new forest or Ramsey assumptions.

This version replaces two independent geometric hypotheses of the
previous conditional theorem by ONE honest description: each small
support-piece carrier is the image of the corresponding gluing copy.
The full-standard carriers are the actual image ranges. All pairwise
overlap equalities then follow directly from free attachment.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I Src N : Type v}

theorem actualPartiteAB_selectedForest_of_attachmentGeometry
    [Fintype N] [Nonempty N]
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
    (hOldCover : DesignatedCoversIrreducibles B D C family)
    (hLocalCover : LocalIrreduciblesCoveredByAInCopies A E f)
    (hBaseStrong :
      ∀ b : RelStructure.Embedding B D, b ∈ family →
        AStrong A D (copyCarrier b))
    {H : Set (Set Src)}
    (outer : I → StrongSupportEmbedding H
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding)
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier
            ((StructuralRamsey.Partite.Attachment.coreEmbedding C
              (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding.comp aE)})
    (active : I → Src ↪ X)
    (hFactor : ∀ i x, outer i x =
      (StructuralRamsey.Partite.Attachment.copyEmbedding C
        (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding
          (active i x))
    (hSourceNonempty : H.Nonempty)
    (hSourceCover : ∀ x : Src,
      ∃ h : Set Src, h ∈ H ∧ x ∈ h)
    (full : I → HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding)
        (W := Y) (I := I)))
    (hFullCarrier : ∀ i : I,
      (full i).carrier =
        Set.range
          (StructuralRamsey.Partite.Attachment.copyEmbedding C
            (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding)
    (hRegularSub : ∀ i : I,
      (outer i).supportPiece.carrier ⊆ (full i).carrier)
    (hRegularEdges : ∀ i : I,
      (outer i).supportPiece.edges ⊆ (full i).edges)
    (hSmallCarrier : ∀ i : I,
      (outer i).supportPiece.carrier =
        copyCarrier (((StructuralRamsey.Partite.Attachment.coreEmbedding C
          (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding).comp
          (f i).toEmbedding))
    (hRegularInCore : ∀ i : I,
      Set.range (outer i) ⊆
        copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding C
          (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding))
    (m : ℕ) (hm : 2 ≤ m)
    (hCoreFinite : Fintype
      (copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding C
        (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding)))
    (hCoreGirth : GirthGT
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding)
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier
            ((StructuralRamsey.Partite.Attachment.coreEmbedding C
              (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding.comp aE)}
      m)
    (hPrevious :
      LocalForestThrough
        (mixedOwnerSmall
          (fun i => (outer i).supportPiece)
          (fun ce : {ce : Set (StructuralRamsey.Partite.Attachment.Vertex
              (activeCarrier A C e.toFunctionEmbedding)
              (W := Y) (I := I)) |
              ∃ aE : RelStructure.Embedding A E.toRelStructure,
                ce = copyCarrier
                  ((StructuralRamsey.Partite.Attachment.coreEmbedding C
                    (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding.comp aE)}
            => ce.1))
        (m - 1))
    {Ambient : Set (Set (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding)
        (W := Y) (I := I)))}
    (hRegularAmbient : ∀ i : I, (full i).edges ⊆ Ambient)
    (hCoreAmbient :
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding)
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier
            ((StructuralRamsey.Partite.Attachment.coreEmbedding C
              (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding.comp aE)}
        ⊆ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (testedOld : HypergraphPiece X → Prop)
    (hOldForest : FiniteMixedForestThrough testedOld m)
    (hOldActiveEdge : ∀ i (h : Set Src), h ∈ H →
      testedOld (HypergraphPiece.oneEdge ((active i) '' h)))
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestB : ∀ q : DesignatedCopy B D C family,
      testedOld (bSupportPiece A q.embedding))
    (selected : N → HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding)
        (W := Y) (I := I)))
    (hSelectedInjective : Function.Injective selected)
    (hSelectedCard : Fintype.card N ≤ m)
    (hSelected : ∀ n : N,
      (∃ aNew : RelStructure.Embedding A
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        selected n = HypergraphPiece.oneEdge (copyCarrier aNew)) ∨
      (∃ bNew : RelStructure.Embedding B
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
        selected n = bSupportPiece A bNew)) :
    ForestOfCopies selected := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let fRel : I → RelStructure.Embedding
      (C.toRelStructure.induce S) E.toRelStructure :=
    fun i => (f i).toEmbedding
  have hRegularOverlap :
      ∀ ⦃i j : I⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (outer i).supportPiece.carrier ∩
            (outer j).supportPiece.carrier := by
    intro i j hij
    rw [hFullCarrier i, hFullCarrier j,
      hSmallCarrier i, hSmallCarrier j]
    exact attachment_copy_copy_intersection
      C.toRelStructure S E.toRelStructure fRel hij
  have hFullCore : ∀ i : I,
      (full i).carrier ∩
        copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding C
          S E f).toEmbedding) =
        (outer i).supportPiece.carrier := by
    intro i
    rw [hFullCarrier i, hSmallCarrier i]
    exact attachment_copy_core_intersection
      C.toRelStructure S E.toRelStructure fRel i
  exact actualPartiteAB_selectedForest_of_factoredCanonical
    A hA B hB D C hPartite hLinear family e E f
    hOldCover hLocalCover hBaseStrong
    outer active hFactor hSourceNonempty hSourceCover
    full hFullCarrier hRegularSub hRegularEdges
    hRegularOverlap hFullCore hRegularInCore
    m hm hCoreFinite hCoreGirth hPrevious
    hRegularAmbient hCoreAmbient hAmbientGirth
    testedOld hOldForest hOldActiveEdge hTestA hTestB
    selected hSelectedInjective hSelectedCard hSelected

end StructuralRamsey.Girth
