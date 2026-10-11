import Girth.ForestActualDesignatedABMixedCases
import Girth.ForestFactoredCanonicalIncrement

/-!
# Actual designated A/B finite-forest increment without local copy coverage

The forest assertion tests transported DESIGNATED B-support pieces and
ambient one-edge A-supports. These are classified directly by
actualDesignatedAB_family_canonicalOwnerCases; unlike arbitrary ambient
B-embeddings, they require neither all-irreducibles-in-designated-B
coverage in the old picture nor local gluing-copy edge coverage.

The genuine free-attachment support geometry, tested old pieces,
mixed local (q-1)-forest, ambient linearity and core girth remain
explicit inputs to the checked finite mixed-owner kernel.
This is a conditional picture-step theorem, not a recursive witness
existence assertion or a tail system-Girth preservation proof.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I Src N : Type v}

/-- Under the genuine relational attachment and exact mixed family
hypotheses, a finite family of actual A- and B-support pieces is a
forest, with no independently chosen owner function or core-edge
coverage hypothesis. -/
theorem actualPartiteDesignatedAB_selectedForest_of_factoredCanonical
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
    (hRegularOverlap :
      ∀ ⦃i j : I⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (outer i).supportPiece.carrier ∩
            (outer j).supportPiece.carrier)
    (hFullCore : ∀ i : I,
      (full i).carrier ∩
        copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding C
          (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding) =
        (outer i).supportPiece.carrier)
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
      (∃ i : I, ∃ q : DesignatedCopy B D C family,
        selected n =
          bSupportPiece A (q.transportToStandard f i).embedding)) :
    ForestOfCopies selected := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex S
      (W := Y) (I := I))) :=
    {t | ∃ aE : RelStructure.Embedding A E.toRelStructure,
      t = copyCarrier (core.comp aE)}
  let standard (i : I) : X ↪
      StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I) :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding
  let coreEdge : {ce : Set (StructuralRamsey.Partite.Attachment.Vertex S
      (W := Y) (I := I)) // ce ∈ K} →
      Set (StructuralRamsey.Partite.Attachment.Vertex S
      (W := Y) (I := I)) :=
    fun ce => ce.1
  letI : Fintype (copyCarrier core) := hCoreFinite
  have hCoreEdgeSub : ∀ ce : {ce : Set _ // ce ∈ K},
      coreEdge ce ⊆ copyCarrier core := by
    intro ce w hw
    rcases ce.2 with ⟨aE, haE⟩
    change w ∈ ce.1 at hw
    rw [haE] at hw
    obtain ⟨u, hu⟩ := hw
    exact ⟨aE u, hu⟩
  have hCases : ∀ n : N,
      (∃ i : I,
        TransportedPiece testedOld (standard i) (selected n) ∧
        SmallOrWholeEdgeBoundary K (copyCarrier core) (selected n)) ∨
      (∃ ce : {ce : Set _ // ce ∈ K},
        selected n = HypergraphPiece.oneEdge (coreEdge ce)) := by
    exact actualDesignatedAB_family_canonicalOwnerCases
      A hA B D C hPartite hLinear family e E f
      hBaseStrong testedOld hTestA hTestB selected hSelected
  exact selectedForest_of_factoredCanonicalMixedCases
    outer active standard hFactor hSourceNonempty hSourceCover
    full hFullCarrier (copyCarrier core) hRegularInCore
    coreEdge selected hSelectedInjective m hm hSelectedCard
    hPrevious hRegularSub hRegularEdges hRegularOverlap hFullCore
    (fun ce => ce.2) hCoreEdgeSub hCoreGirth
    (fun i ce h => hRegularAmbient i h)
    (fun ce => hCoreAmbient ce.2) hAmbientGirth
    testedOld hOldForest hOldActiveEdge hCases

end StructuralRamsey.Girth
