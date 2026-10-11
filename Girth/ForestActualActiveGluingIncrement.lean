import Girth.ForestActualOldFullIncrement
import Girth.ForestActualSmallGluingCarrier

/-!
# Conditional actual A/B forest theorem with no independent carrier geometry

Every gluing map in the genuine picture step is a strong image of
the ENTIRE true active source, attached through the standard picture.
Assuming exact source range onto the true active subsystem (rather
than just its part support), the gluing image in the core is automatic.
The underlying old full picture supplies all standard carriers and
source support inclusions. Free attachment supplies pair intersections.

The resulting finite selected A/B forest theorem no longer needs
separate small-carrier, full-carrier, small-in-full, or overlap
hypotheses. Its remaining genuine inputs are local mixed foresthood,
source/core girth, old q-forest, tested old A/B pieces, and ambient
support/girth. This is STILL CONDITIONAL on the recursive local Ramsey
witness and its train invariants.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I Src N : Type v}

theorem actualPartiteAB_selectedForest_of_actualActiveGluing
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
  exact actualPartiteAB_selectedForest_of_oldFullSupport
    A hA B hB D C hPartite hLinear family e E f
    hOldCover hLocalCover hBaseStrong
    outer active hFactor hSourceNonempty hSourceCover
    oldFull hOldFull hSourceOldSupport
    hSmallCarrier hRegularInCore m hm hCoreFinite
    hCoreGirth hPrevious hRegularAmbient hCoreAmbient
    hAmbientGirth testedOld hOldForest hOldActiveEdge
    hTestA hTestB selected hSelectedInjective hSelectedCard
    hSelected

end StructuralRamsey.Girth
