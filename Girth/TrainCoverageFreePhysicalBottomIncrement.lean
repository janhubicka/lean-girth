import Girth.TrainCoverageFreePhysicalStage
import Girth.ForestRecursiveOutputGirthWeak
import Girth.TrainSelectedPictureStageForest
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact coverage-free bottom mixed-forest increment

The checked original ForestTailStage.activeAttachment_bottom_invariants_of_intrinsic
never uses the recursive mixedCoverage field. Its proof depends only
on the actual selected B-copy family, the old mixed finite-set forest,
A-irreducibility, the true partite free attachment, base strongness,
the local predecessor forests, core support girth and the cutoff-two
core linearity and strongness of the gluing copies.

Here the SAME proof is applied to the weaker standalone F_t picture
stage. It still derives, at the SAME cutoff q:
  * complete new selected B/A mixed finite-SET forest through q;
  * ordinary complete ambient A-support girth >q;
  * A-strongness of every transported ORIGINAL selected B-copy.

No core mixed irreducible-coverage input is asked for or smuggled in.
The intermediate stage can therefore include a genuine arbitrary
F_t witness, not only one produced by the stronger recursive
ForestTailStage. This is the central bottom forest ingredient of
the coverage-free F_t -> R_t conversion.

This theorem does NOT independently produce a selected Ramsey
PictureStep, the core partite train, or full output system-girth;
those are separate exact interfaces.
-/

/-!
Physical A-copy projection port: the genuine selected B/A mixed
forest and ordinary support-girth increment keeps every original
physical edge and selected B label. Its only changed geometric
input is ProjectsACopies in place of full ordered IsPartiteOver.
The new forest/girth transfer lemmas are source-level UNCOMPILED.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- A coverage-free old stage has exactly the hypotheses needed
by the existing physical mixed-forest increment. Every ambient
A-edge is still tested; the resulting selected original B-copy
strongness and ordinary support girth are genuine conclusions. -/
theorem PhysicalForestStage.activeAttachment_bottom_invariants_of_intrinsic
    (stage : PhysicalForestStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) [Finite UA]
    (hBaseLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty)
    (E : StructuralRamsey.Partite.System L P Y) [Finite Y]
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family, b ∈ stage.selected →
      AStrong A D (copyCarrier b.base))
    (hk : 2 ≤ t.headD 0)
    (hLocal : t.headD 0 = 2 ∨
      ((∃ e₀ e₁ : Set (activeCarrier A stage.system e.toFunctionEmbedding),
          e₀ ∈ supportCopies A
            (stage.system.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
          e₁ ∈ supportCopies A
            (stage.system.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
          e₀ ≠ e₁) ∧
        Function.Injective (fun i => bSupportPiece A (f i).toEmbedding) ∧
        FiniteMixedForestThrough
          (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (t.headD 0 - 1)))
    (hCoreGirth : 2 < t.headD 0 →
      GirthGT (supportCopies A E.toRelStructure) (t.headD 0))
    (hTwoGeometry : t.headD 0 = 2 →
      ALinear A E.toRelStructure ∧
        ∀ i, AStrong A E.toRelStructure (copyCarrier (f i).toEmbedding)) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let attached := StructuralRamsey.Partite.Attachment.attach stage.system S E f
    let selected := transportedSelectedCopies B D stage.system family stage.selected S E f
    FiniteMixedForestThrough (testedAB A B D attached family selected) (t.headD 0) ∧
      GirthGT (supportCopies A attached.toRelStructure) (t.headD 0) ∧
      ∀ b : DesignatedCopy B D attached family, b ∈ selected →
        AStrong A attached.toRelStructure (copyCarrier b.embedding) := by
  classical
  let : Fintype Y := Fintype.ofFinite Y
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let attached := StructuralRamsey.Partite.Attachment.attach stage.system S E f
  let selected := transportedSelectedCopies B D stage.system family stage.selected S E f
  change FiniteMixedForestThrough (testedAB A B D attached family selected) (t.headD 0) ∧
    GirthGT (supportCopies A attached.toRelStructure) (t.headD 0) ∧
    ∀ b : DesignatedCopy B D attached family, b ∈ selected →
      AStrong A attached.toRelStructure (copyCarrier b.embedding)
  have hCore : GirthGT (supportCopies A E.toRelStructure) (t.headD 0) := by
    by_cases hTwo : t.headD 0 = 2
    · rw [hTwo]
      exact girthGT_two_of_aLinear A E.toRelStructure (hTwoGeometry hTwo).1
    · exact hCoreGirth (by omega)
  have hRaw := actualPartiteDesignatedAB_forest_and_girth_of_localGeometry_projected
    A hA B D stage.system stage.projectsACopies hBaseLinear family stage.selected
    e hRigid hActive E f hBaseStrong (t.headD 0) hk
    (fun hTwo => (hTwoGeometry hTwo).2) hLocal hCore
    (testedAB A B D stage.system family stage.selected) stage.bottomForest
    (fun a => Or.inl ⟨a, rfl⟩)
    (fun b hb => Or.inr ⟨b, hb, rfl⟩)
  have hForest : FiniteMixedForestThrough
      (testedAB A B D attached family selected) (t.headD 0) := by
    intro s hs hCard
    apply hRaw.1 s ?_ hCard
    intro piece hPiece
    exact (testedAB_transportedSelectedCopies_iff A B D stage.system family
      stage.selected S E f piece).mp (hs piece hPiece)
  refine ⟨hForest, hRaw.2, ?_⟩
  intro b hb
  exact aStrong_of_finiteMixedForestThrough A b.embedding
    (testedAB A B D attached family selected) (t.headD 0) hk hForest
    (Or.inr ⟨b, hb, rfl⟩) (fun a => Or.inl ⟨a, rfl⟩)


end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
