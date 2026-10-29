import Girth.ForestActualRecursiveSupport
import Girth.ForestActualDesignatedTrueActiveIncrement

/-!
# The actual forest increment from relational local-witness clauses

This is the recursive picture step with its support implementation filled
in: the source is the true active induced structure; the source maps are
subtype inclusions; the gluing maps are the actual local embeddings followed
by the core embedding; and the old full piece contains every old A-edge.
The old B-family is the prescribed selected subfamily. Unselected projected
lifts impose neither a tested-piece condition nor a base-strongness condition.

At cutoff two the predecessor forest is automatic. At larger cutoffs the
local witness supplies its mixed finite-set forest bound, and the source
has two distinct support edges. Physical local copies must be indexed
injectively before attachment. No ambient core edge is removed.

The theorem proves the complete finite-set forest invariant for one actual
step. Existence and the Ramsey property of the local witness, and higher
train cycle conditions, are not part of its conclusion.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- A genuine relational local witness gives the full actual designated-B
and ambient-A finite-set forest increment. The two disjuncts are the
cutoff-two base and the larger-cutoff recursive local input. -/
theorem actualPartiteDesignatedAB_mixedForest_of_relationalLocal
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D) (hLinear : ALinear A D)
    (family : Set (RelStructure.Embedding B D))
    (selectedOld : Set (DesignatedCopy B D C family))
    (e : RelStructure.Embedding A D)
    (hActive : (activeCarrier A C e.toFunctionEmbedding).Nonempty)
    (E : StructuralRamsey.Partite.System L P Y) [Fintype Y]
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family, q ∈ selectedOld →
      AStrong A D (copyCarrier q.base))
    (hLocalStrong : ∀ i, AStrong A E.toRelStructure
      (copyCarrier (f i).toEmbedding))
    (m : ℕ) (hm : 2 ≤ m)
    (hLocal : m = 2 ∨
      ((∃ e₀ e₁ : Set (activeCarrier A C e.toFunctionEmbedding),
          e₀ ∈ supportCopies A
            (C.induce (activeCarrier A C e.toFunctionEmbedding)).toRelStructure ∧
          e₁ ∈ supportCopies A
            (C.induce (activeCarrier A C e.toFunctionEmbedding)).toRelStructure ∧
          e₀ ≠ e₁) ∧
        Function.Injective (fun i => bSupportPiece A (f i).toEmbedding) ∧
        FiniteMixedForestThrough
          (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (m - 1)))
    (hCoreGirth : GirthGT (supportCopies A E.toRelStructure) m)
    (hAmbientGirth : GirthGT
      (supportCopies A
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure) 2)
    (testedOld : HypergraphPiece X → Prop)
    (hOldForest : FiniteMixedForestThrough testedOld m)
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestB : ∀ q : DesignatedCopy B D C family, q ∈ selectedOld →
      testedOld (bSupportPiece A q.embedding)) :
    FiniteMixedForestThrough
      (fun T : HypergraphPiece
        (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I)) =>
        (∃ aNew : RelStructure.Embedding A
          (StructuralRamsey.Partite.Attachment.attach C
            (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
          T = HypergraphPiece.oneEdge (copyCarrier aNew)) ∨
        (∃ i : I, ∃ q : DesignatedCopy B D C family, q ∈ selectedOld ∧
          T = bSupportPiece A (q.transportToStandard f i).embedding)) m := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let attached := StructuralRamsey.Partite.Attachment.attach C S E f
  let core := (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let H := supportCopies A (C.induce S).toRelStructure
  let K := mappedSupportCopies A E.toRelStructure attached.toRelStructure core
  let outer := fun i => mappedStrongASupportEmbedding A
    (f i).toEmbedding (hLocalStrong i) core
  let active : I → S ↪ X := fun _ => ⟨Subtype.val, Subtype.val_injective⟩
  let standard := fun i =>
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding
  let full := fun i => (fullASupportPiece A C.toRelStructure).map (standard i)
  let fRel : I → Embedding (C.toRelStructure.induce S) E.toRelStructure :=
    fun i => (f i).toEmbedding
  have hFactor : ∀ i (x : S), outer i x =
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
        (active i x) := by
    intro i x
    exact (StructuralRamsey.Partite.Attachment.copy_extends C S E f i x).symm
  have hSourceNonempty : H.Nonempty :=
    actualRecursiveActiveSupport_nonempty A C e.toFunctionEmbedding hActive
  have hSourceCover : ∀ x : S, ∃ h : Set S, h ∈ H ∧ x ∈ h :=
    actualRecursiveActiveSupport_cover A C e.toFunctionEmbedding
  have hActiveRange : ∀ i, Set.range (active i) = S := by
    intro i
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hSourceOldSupport : ∀ i (h : Set S), h ∈ H →
      (active i) '' h ∈ (fullASupportPiece A C.toRelStructure).edges := by
    intro i h hh
    exact activeASupport_image_in_old A C.toRelStructure S hh
  have hSmallCarrier : ∀ i, (outer i).supportPiece.carrier =
      copyCarrier (core.comp (f i).toEmbedding) := by
    intro i
    exact actualSmallGluing_supportCarrier_eq_coreCopy A C D e E f
      outer active hFactor hActiveRange i
  have hRangeCore : ∀ i, Set.range (outer i) ⊆ copyCarrier core := by
    intro i x hx
    obtain ⟨s, rfl⟩ := hx
    exact ⟨f i s, rfl⟩
  have hFullCarrier : ∀ i, (full i).carrier = Set.range (standard i) := by
    intro i
    exact attachment_full_supportPiece_carrier C.toRelStructure S E.toRelStructure fRel
      (fullASupportPiece A C.toRelStructure) rfl i
  have hSmallSub : ∀ i, (outer i).supportPiece.carrier ⊆ (full i).carrier := by
    intro i
    exact (outer i).supportPiece_carrier_subset_standard
      (active i) (standard i) (hFactor i) (fullASupportPiece A C.toRelStructure)
      (fun _ => Set.mem_univ _)
  have hSmallEdges : ∀ i, (outer i).supportPiece.edges ⊆ (full i).edges := by
    intro i
    exact (outer i).supportPiece_edges_subset_standard
      (active i) (standard i) (hFactor i) (fullASupportPiece A C.toRelStructure)
      (hSourceOldSupport i)
  have hRegularOverlap : ∀ ⦃i j : I⦄, i ≠ j →
      (full i).carrier ∩ (full j).carrier =
        (outer i).supportPiece.carrier ∩ (outer j).supportPiece.carrier := by
    intro i j hij
    rw [hFullCarrier i, hFullCarrier j, hSmallCarrier i, hSmallCarrier j]
    exact attachment_copy_copy_intersection C.toRelStructure S E.toRelStructure fRel hij
  have hFullCore : ∀ i, (full i).carrier ∩ copyCarrier core =
      (outer i).supportPiece.carrier := by
    intro i
    rw [hFullCarrier i, hSmallCarrier i]
    exact attachment_copy_core_intersection C.toRelStructure S E.toRelStructure fRel i
  have hCoreEdgeSub : ∀ ce : {ce : Set _ // ce ∈ K}, ce.1 ⊆ copyCarrier core := by
    intro ce x hx
    obtain ⟨a, ha⟩ := ce.2
    rw [ha] at hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨a u, hu⟩
  have hPrevious : LocalForestThrough
      (mixedOwnerSmall (fun i => (outer i).supportPiece)
        (fun ce : {ce : Set _ // ce ∈ K} => ce.1)) (m - 1) := by
    rcases hLocal with hTwo | ⟨⟨e₀, e₁, he₀, he₁, hne⟩, hCopies, hForest⟩
    · rw [hTwo]
      exact actualRecursiveLocalForest_one _
    · exact actualRecursiveMixedLocalForest A
        (fun i => (f i).toEmbedding) hLocalStrong core
        hCopies e₀ e₁ he₀ he₁ hne (m - 1) hForest
  have hCoreGirth' : GirthGT K m :=
    girthGT_mappedSupportCopies A E.toRelStructure attached.toRelStructure
      core hCoreGirth
  have hRegularAmbient : ∀ i,
      ((fullASupportPiece A C.toRelStructure).map
        (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding.toFunctionEmbedding).edges ⊆
        supportCopies A attached.toRelStructure := by
    intro i h hh
    obtain ⟨hOld, hhOld, rfl⟩ := hh
    exact aSupport_image_of_embedding A C.toRelStructure attached.toRelStructure
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding hhOld
  have hCoreAmbient : K ⊆ supportCopies A attached.toRelStructure := by
    rintro h ⟨a, rfl⟩
    exact ⟨core.comp a, rfl⟩
  have hOldActiveEdge : ∀ i (h : Set S), h ∈ H →
      testedOld (HypergraphPiece.oneEdge ((active i) '' h)) := by
    intro i h hh
    obtain ⟨a, ha⟩ := activeASupport_image_in_old A C.toRelStructure S hh
    change Subtype.val '' h = copyCarrier a at ha
    change testedOld (HypergraphPiece.oneEdge (Subtype.val '' h))
    rw [ha]
    exact hTestA a
  letI : Fintype (copyCarrier core) := Set.fintypeRange core
  intro s hTest hCard
  by_cases hEmpty : s = ∅
  · subst s
    haveI : IsEmpty {T : HypergraphPiece
        (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)) //
        T ∈ (∅ : Finset _)} :=
      ⟨fun T => (Finset.notMem_empty T.1) T.2⟩
    exact forestOfCopies_of_subsingleton _
  · have hNonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let N := {T : HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I)) // T ∈ s}
    letI : Nonempty N := by
      obtain ⟨T, hT⟩ := hNonempty
      exact ⟨⟨T, hT⟩⟩
    have hCases : ∀ n : N,
        (∃ i, TransportedPiece testedOld (standard i) n.1 ∧
          SmallOrWholeEdgeBoundary K (copyCarrier core) n.1) ∨
        (∃ ce : {ce : Set _ // ce ∈ K}, n.1 = HypergraphPiece.oneEdge ce.1) := by
      intro n
      rcases hTest n.1 n.2 with ⟨aNew, hNew⟩ | ⟨i, q, hq, hNew⟩
      · rcases attached_actualACopy_coreOr_testedStandardBoundary
          A hA D C hPartite hLinear e E f testedOld hTestA aNew with
          hCore | ⟨i, hOld, hBoundary⟩
        · exact Or.inr ⟨⟨copyCarrier aNew, hCore⟩, hNew⟩
        · left
          refine ⟨i, ?_, ?_⟩
          · rw [hNew]
            exact hOld
          · rw [hNew]
            exact hBoundary
      · obtain ⟨hOld, hBoundary⟩ := transportedDesignatedB_testedOwner_and_boundary
          A B D C family e E f q (hBaseStrong q hq) testedOld (hTestB q hq) i
        left
        refine ⟨i, ?_, ?_⟩
        · rw [hNew]
          exact hOld
        · rw [hNew]
          exact hBoundary
    exact selectedForest_of_factoredCanonicalMixedCases
      outer active standard hFactor hSourceNonempty hSourceCover
      full hFullCarrier (copyCarrier core) hRangeCore
      (fun ce : {ce : Set _ // ce ∈ K} => ce.1)
      (fun n : N => n.1) Subtype.val_injective m hm
      (by simpa [N] using hCard) hPrevious hSmallSub hSmallEdges
      hRegularOverlap hFullCore (fun ce => ce.2) hCoreEdgeSub hCoreGirth'
      (fun i _ hh => hRegularAmbient i hh) (fun ce => hCoreAmbient ce.2) hAmbientGirth
      testedOld hOldForest hOldActiveEdge hCases

end StructuralRamsey.Girth
