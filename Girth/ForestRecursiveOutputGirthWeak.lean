import Girth.ForestRecursiveOutputGirth
import Girth.ForestActualRecursiveIncrementWeak
import Girth.TrainCoverageFreeACopyGeometry
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
Physical projected-copy version of BOTH genuine old forest-to-girth
lemmas. The old full IsPartiteOver condition occurred only in the
active-carrier strongness lemma and the original A-copy boundary
lemma; both now have weak versions. The full finite mixed forest
construction and exact selected labels remain unchanged.
UNCOMPILED SOURCE-LEVEL PROOF CANDIDATES.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Derive the whole attached support's girth greater than two from the
old mixed invariant and the actual core/strong-image geometry. -/
theorem actualActiveAttachment_girthGT_two_of_mixedOld_projected
    (A : RelStructure L UA) (hA : A.Irreducible)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (hProjected : ProjectsACopies A D C) (hBaseLinear : ALinear A D)
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
  have hOutput := activeAttachment_geometry_of_projectedACopies
    A D C hA hProjected hBaseLinear e hRigid E f
    hOldLinear hCoreLinear hLocalStrong
  exact girthGT_two_of_aLinear A _ hOutput.1

/-- The actual selected-family increment with its output girth premise
discharged. At larger cutoffs local strongness is derived from the local
mixed invariant; the resulting output has ordinary girth through m as well. -/
theorem actualPartiteDesignatedAB_forest_and_girth_of_localGeometry_projected
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hProjected : ProjectsACopies A D C) (hLinear : ALinear A D)
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
  have hAmbient := actualActiveAttachment_girthGT_two_of_mixedOld_projected
    A hA D C hProjected hLinear e hRigid E f hLocalStrong
    m hm hCoreGirth testedOld hOldForest hTestA
  have hOutput := actualPartiteDesignatedAB_mixedForest_of_relationalLocal_projected
    A hA B D C hProjected hLinear family selectedOld e hActive E f
    hBaseStrong hLocalStrong m hm hLocal hCoreGirth hAmbient
    testedOld hOldForest hTestA hTestB
  refine ⟨hOutput, ?_⟩
  apply girthGT_of_finiteMixedForestThrough _ _ m hOutput
  rintro edge ⟨a, rfl⟩
  exact Or.inl ⟨a, rfl⟩


end StructuralRamsey.Girth
