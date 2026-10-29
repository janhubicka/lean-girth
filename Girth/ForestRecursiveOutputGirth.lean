import Girth.ForestActualRecursiveIncrement
import Girth.ForestAllSupportGirth
import Girth.ForestMixedAStrong
import Girth.ActiveCarrierStrong
import Girth.LinearityGirthTwo

/-!
# Ordinary support girth supplied by the actual recursive geometry

The mixed finite-set invariant tests every ambient A-edge. Consequently it
already implies ordinary support girth through the same cutoff. This follows
by applying the invariant to the edges of a purported short Berge cycle and
using the existing girth theorem for a forest of one-edge pieces.

For an active attachment, the old mixed invariant and core ordinary girth
therefore supply old/core A-linearity. Base A-linearity and rigidity of the
active profile make the true active source strong; strong local images then
give actual output A-linearity by the checked attachment theorem. Thus the
ordinary output girth greater than two needed by the increment is derived
before using the output forest conclusion.

At a cutoff greater than two the local mixed forest bound also supplies
strongness of each local image, including against uncovered ambient edges.
Only the cutoff-two local constructor must provide that strongness separately.
The larger-cutoff core girth bound remains explicit: a mixed forest bound
through m - 1 does not by itself justify ordinary girth greater than m.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {W : Type v}

/-- Testing every one-edge piece in the finite mixed forest invariant
excludes every ambient Berge cycle through the same cutoff. -/
theorem girthGT_of_finiteMixedForestThrough
    (H : Set (Set W)) (tested : HypergraphPiece W → Prop) (m : ℕ)
    (hForest : FiniteMixedForestThrough tested m)
    (hEdges : ∀ e : Set W, e ∈ H → tested (HypergraphPiece.oneEdge e)) :
    GirthGT H m := by
  classical
  rintro ⟨c, hLength⟩
  let F : ULift.{v} (Fin c.length) → HypergraphPiece W :=
    fun i => HypergraphPiece.oneEdge (c.edge i.down)
  let S := {P : HypergraphPiece W // P ∈ finitePieceImage F}
  have hSelected : ForestOfCopies (fun P : S => P.1) :=
    hForest.image tested m F (fun i => hEdges _ (c.edge_mem i.down))
      (by simpa only [Fintype.card_ulift, Fintype.card_fin] using hLength)
  have hEach : ∀ P : S, GirthGT P.1.edges m := by
    intro P
    have hP : P.1 ∈ Finset.univ.image F := P.2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hP
    rw [← hi]
    apply girthGT_of_edgeFamily_subsingleton
    intro e he f hf
    have he' : e = c.edge i.down := he
    have hf' : f = c.edge i.down := hf
    exact he'.trans hf'.symm
  have hGirth := girthGT_union_of_forest (fun P : S => P.1) hSelected m hEach
  apply hGirth
  refine ⟨c.ofEdgeMem ?_, hLength⟩
  intro i
  have hFi : F ⟨i⟩ ∈ finitePieceImage F := by
    exact Finset.mem_image.mpr ⟨⟨i⟩, Finset.mem_univ _, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨F ⟨i⟩, hFi⟩, rfl⟩

/-- Two distinct tested physical pieces have an allowed intersection once
the finite-set forest bound includes pairs. -/
theorem FiniteMixedForestThrough.allowedIntersection_of_ne
    {tested : HypergraphPiece W → Prop} {m : ℕ}
    (hForest : FiniteMixedForestThrough tested m) (hm : 2 ≤ m)
    (F G : HypergraphPiece W) (hF : tested F) (hG : tested G) (hne : F ≠ G) :
    AllowedIntersection F G := by
  classical
  let s : Finset (HypergraphPiece W) := {F, G}
  have hSelected := hForest s (by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hF
    · have hPG : P = G := Finset.mem_singleton.mp hP
      simpa only [hPG] using hG) ((Finset.card_le_two (a := F) (b := G)).trans hm)
  let a : {P : HypergraphPiece W // P ∈ s} := ⟨F, by simp [s]⟩
  let b : {P : HypergraphPiece W // P ∈ s} := ⟨G, by simp [s]⟩
  exact hSelected.pairwiseAllowed
    (fun h : a = b => hne (congrArg Subtype.val h))

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

/-- A tested full B-support is A-strong if every actual ambient A-edge is
also tested. Equal physical pieces are handled directly as one-edge pieces. -/
theorem aStrong_of_finiteMixedForestThrough
    (A : RelStructure L UA) {B : RelStructure L VB} {C : RelStructure L W}
    (b : Embedding B C) (tested : HypergraphPiece W → Prop)
    (m : ℕ) (hm : 2 ≤ m) (hForest : FiniteMixedForestThrough tested m)
    (hB : tested (bSupportPiece A b))
    (hA : ∀ a : Embedding A C,
      tested (HypergraphPiece.oneEdge (copyCarrier a))) :
    AStrong A C (copyCarrier b) := by
  apply aStrong_of_mixed_support_intersections A b
  intro a
  by_cases hEq : bSupportPiece A b = HypergraphPiece.oneEdge (copyCarrier a)
  · rw [hEq]
    right
    exact ⟨copyCarrier a, rfl, rfl, Set.inter_self _⟩
  · exact hForest.allowedIntersection_of_ne hm _ _ hB (hA a) hEq

/-- Derive the whole attached support's girth greater than two from the
old mixed invariant and the actual core/strong-image geometry. -/
theorem actualActiveAttachment_girthGT_two_of_mixedOld
    (A : RelStructure L UA) (hA : A.Irreducible)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hLocalStrong : ∀ i, AStrong A E.toRelStructure
      (copyCarrier (f i).toEmbedding))
    (m : ℕ) (hm : 2 ≤ m)
    (hCoreGirth : GirthGT (supportCopies A E.toRelStructure) m)
    (testedOld : HypergraphPiece X → Prop)
    (hOldForest : FiniteMixedForestThrough testedOld m)
    (hTestA : ∀ a : Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier a))) :
    GirthGT (supportCopies A
      (StructuralRamsey.Partite.Attachment.attach C
        (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure) 2 := by
  have hOldGirth : GirthGT (supportCopies A C.toRelStructure) m := by
    apply girthGT_of_finiteMixedForestThrough _ testedOld m hOldForest
    rintro edge ⟨a, rfl⟩
    exact hTestA a
  have hOldLinear := aLinear_of_girthGT_two A C.toRelStructure
    (girthGT_mono hOldGirth hm)
  have hCoreLinear := aLinear_of_girthGT_two A E.toRelStructure
    (girthGT_mono hCoreGirth hm)
  have hOutput := activeAttachment_geometry_of_base_aLinear
    A D C hA hPartite hBaseLinear e hRigid E f
    hOldLinear hCoreLinear hLocalStrong
  exact girthGT_two_of_aLinear A _ hOutput.1

/-- The actual selected-family increment with its output girth premise
discharged. At larger cutoffs local strongness is derived from the local
mixed invariant; the resulting output has ordinary girth through m as well. -/
theorem actualPartiteDesignatedAB_forest_and_girth_of_localGeometry
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D) (hLinear : ALinear A D)
    (family : Set (Embedding B D))
    (selectedOld : Set (DesignatedCopy B D C family))
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A C e.toFunctionEmbedding).Nonempty)
    (E : StructuralRamsey.Partite.System L P Y) [Fintype Y]
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family, q ∈ selectedOld →
      AStrong A D (copyCarrier q.base))
    (m : ℕ) (hm : 2 ≤ m)
    (hTwoStrong : m = 2 → ∀ i, AStrong A E.toRelStructure
      (copyCarrier (f i).toEmbedding))
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
    (testedOld : HypergraphPiece X → Prop)
    (hOldForest : FiniteMixedForestThrough testedOld m)
    (hTestA : ∀ a : Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier a)))
    (hTestB : ∀ q : DesignatedCopy B D C family, q ∈ selectedOld →
      testedOld (bSupportPiece A q.embedding)) :
    let attached := StructuralRamsey.Partite.Attachment.attach C
      (activeCarrier A C e.toFunctionEmbedding) E f
    let tested : HypergraphPiece
        (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I)) → Prop :=
      fun T =>
        (∃ a : Embedding A attached.toRelStructure,
          T = HypergraphPiece.oneEdge (copyCarrier a)) ∨
        (∃ i : I, ∃ q : DesignatedCopy B D C family, q ∈ selectedOld ∧
          T = bSupportPiece A (q.transportToStandard f i).embedding)
    FiniteMixedForestThrough tested m ∧
      GirthGT (supportCopies A attached.toRelStructure) m := by
  have hLocalStrong : ∀ i, AStrong A E.toRelStructure
      (copyCarrier (f i).toEmbedding) := by
    intro i
    by_cases hTwo : m = 2
    · exact hTwoStrong hTwo i
    · rcases hLocal with hTwo' | ⟨_, _, hForest⟩
      · exact (hTwo hTwo').elim
      · exact aStrong_of_finiteMixedForestThrough A (f i).toEmbedding
          (RelationalMixedSupportTest A (fun i => (f i).toEmbedding))
          (m - 1) (by omega) hForest
          (Or.inl ⟨i, rfl⟩) (fun a => Or.inr ⟨a, rfl⟩)
  have hAmbient := actualActiveAttachment_girthGT_two_of_mixedOld
    A hA D C hPartite hLinear e hRigid E f hLocalStrong
    m hm hCoreGirth testedOld hOldForest hTestA
  have hOutput := actualPartiteDesignatedAB_mixedForest_of_relationalLocal
    A hA B D C hPartite hLinear family selectedOld e hActive E f
    hBaseStrong hLocalStrong m hm hLocal hCoreGirth hAmbient
    testedOld hOldForest hTestA hTestB
  refine ⟨hOutput, ?_⟩
  apply girthGT_of_finiteMixedForestThrough _ _ m hOutput
  rintro edge ⟨a, rfl⟩
  exact Or.inl ⟨a, rfl⟩

end StructuralRamsey.Girth
