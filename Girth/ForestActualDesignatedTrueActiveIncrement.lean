import Girth.ForestActualDesignatedDirectIncrement
import Girth.ForestActualSmallGluingCarrier
import Girth.ForestStandardSupportFactor
import Girth.ForestAttachmentSupportPairs

/-!
# Complete true-active gluing geometry for the designated A/B forest increment

The finite mixed forest increment needs no local edge-covered gluing family.
For the actual partite attachment, a full old support piece is transported
into every standard copy. If the active source embeddings cover exactly the
TRUE active carrier, the small gluing support is its core image, and all
other carrier/edge/overlap conditions follow from the free attachment.
The only combinatorial forest inputs are the previous mixed local and
old-picture forest hypotheses, together with genuine ambient/core girth.

This is conditional on an existing local witness; it does not establish
that witness's Ramsey property or any tail system-Girth assertion.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I Src N : Type v}

theorem actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull
    [Fintype N] [Nonempty N]
    (A : RelStructure L UA)
    (hA : A.Irreducible) [Finite UA]
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
    (hActiveRange : ∀ i : I,
      Set.range (active i) = activeCarrier A C e.toFunctionEmbedding)
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
    (hRegularAmbient : ∀ i : I,
      (oldFull.map
        ((StructuralRamsey.Partite.Attachment.copyEmbedding C
          (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding.toFunctionEmbedding)).edges ⊆ Ambient)
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
      (∃ i : I, ∃ q : DesignatedCopy B D C family,
        selected n =
          bSupportPiece A (q.transportToStandard f i).embedding)) :
    ForestOfCopies selected := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  have hSmallCarrier : ∀ i : I,
      (outer i).supportPiece.carrier =
        copyCarrier (core.comp (f i).toEmbedding) := by
    intro i
    exact actualSmallGluing_supportCarrier_eq_coreCopy
      A C D e E f outer active hFactor hActiveRange i
  have hRegularInCore : ∀ i : I,
      Set.range (outer i) ⊆ copyCarrier core := by
    intro i x hx
    change x ∈ (outer i).supportPiece.carrier at hx
    rw [hSmallCarrier i] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨(f i).toEmbedding y, hy⟩
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
      (full i).carrier ∩ copyCarrier core =
        (outer i).supportPiece.carrier := by
    intro i
    rw [hFullCarrier i, hSmallCarrier i]
    exact attachment_copy_core_intersection
      C.toRelStructure S E.toRelStructure fRel i
  exact actualPartiteDesignatedAB_selectedForest_of_factoredCanonical
    A hA B D C hPartite hLinear family e E f
    hBaseStrong
    outer active hFactor hSourceNonempty hSourceCover
    full hFullCarrier hSmallSub hSmallEdges
    hRegularOverlap hFullCore hRegularInCore
    m hm hCoreFinite hCoreGirth hPrevious
    hRegularAmbient hCoreAmbient hAmbientGirth
    testedOld hOldForest hOldActiveEdge hTestA hTestB
    selected hSelectedInjective hSelectedCard hSelected

end StructuralRamsey.Girth
