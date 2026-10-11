import Girth.ForestActualPartiteGeometryIncrement
import Girth.ForestStandardSupportFactor
import Girth.ForestAttachmentSupportPairs

/-!
# Genuine old full support removes further free-attachment forest assumptions

In the circulation picture step every full standard support piece is
the image of ONE full old support piece. The latter has carrier the
entire old picture; all source gluing support edges are already old
support edges. Hence the small gluing carrier and edge inclusions
in a full standard picture are derived by factorization, and the
full carrier is the actual image of the standard embedding.

Together with checked free-attachment overlap geometry, this
removes independent full-carrier and small-to-full inclusion
hypotheses from the conditional actual A/B forest increment.
The only remaining geometric input is that each SMALL gluing piece
has the actual core gluing-carrier image. The local mixed forest,
girth and Ramsey recursion remain explicit.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I Src N : Type v}

theorem actualPartiteAB_selectedForest_of_oldFullSupport
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
    (oldFull : HypergraphPiece X)
    (hOldFull : oldFull.carrier = Set.univ)
    (hSourceOldSupport : ∀ i : I, ∀ h : Set Src, h ∈ H →
      (active i) '' h ∈ oldFull.edges)
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
  let standard (i : I) : X ↪
      StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I) :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding
  let full : I → HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)) :=
    fun i => oldFull.map (standard i)
  have hFullCarrier : ∀ i : I,
      (full i).carrier =
        Set.range
          (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding := by
    intro i
    exact attachment_full_supportPiece_carrier
      C.toRelStructure S E.toRelStructure fRel oldFull hOldFull i
  have hSourceCarrier (i : I) :
      ∀ x : Src, active i x ∈ oldFull.carrier := by
    intro x
    rw [hOldFull]
    exact Set.mem_univ _
  have hSmallSub (i : I) :
      (outer i).supportPiece.carrier ⊆ (full i).carrier := by
    exact (outer i).supportPiece_carrier_subset_standard
      (active i) (standard i) (hFactor i) oldFull (hSourceCarrier i)
  have hSmallEdges (i : I) :
      (outer i).supportPiece.edges ⊆ (full i).edges := by
    exact (outer i).supportPiece_edges_subset_standard
      (active i) (standard i) (hFactor i) oldFull
      (hSourceOldSupport i)
  exact actualPartiteAB_selectedForest_of_attachmentGeometry
    A hA B hB D C hPartite hLinear family e E f
    hOldCover hLocalCover hBaseStrong
    outer active hFactor hSourceNonempty hSourceCover
    full hFullCarrier hSmallSub hSmallEdges hSmallCarrier
    hRegularInCore m hm hCoreFinite hCoreGirth hPrevious
    hRegularAmbient hCoreAmbient hAmbientGirth
    testedOld hOldForest hOldActiveEdge hTestA hTestB
    selected hSelectedInjective hSelectedCard hSelected

end StructuralRamsey.Girth
