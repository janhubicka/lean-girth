import Girth.TrainSelectedPictureStageAssembly
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Selected base coverage removes a spurious "all family copies strong" premise

The actual ForestTailStage stores strongness of SELECTED target copies,
whereas some earlier checked physical supreme-transfer lemmas request
strongness of every prescribed base-family embedding.

The extra input is not an independent strongness property. It follows
if every prescribed base family member has a selected LIFT: the
already present ActiveAttachmentBounds.baseStrong is then enough.
This base-coverage invariant holds in the initial disjoint picture
and is preserved by every selected TransitionEmbedding.

It must be carried explicitly through the finite picture pass.
No claim is made that an arbitrary stage's selected family covers
its prescribed base family.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every prescribed base B-copy still has one selected lift in the
stage. This is a property of the selected set and base projection,
NOT a consequence of selected strongness alone. -/
def ForestTailStage.CoversBase
    (stage : ForestTailStage A B D family t targetTrain allowed) : Prop :=
  ∀ b : Embedding B D, b ∈ family →
    ∃ q : DesignatedCopy B D stage.system family,
      q ∈ stage.selected ∧ q.base = b

/-- Selected train transitions retain the prescribed base of every
selected lifted copy and hence preserve base-family coverage. -/
theorem TransitionEmbedding.coversBase
    {S T : ForestTailStage A B D family t targetTrain allowed}
    (g : TransitionEmbedding S T)
    (h : S.CoversBase) : T.CoversBase := by
  intro b hb
  obtain ⟨q, hq, hBase⟩ := h b hb
  refine ⟨mapDesignated g.toPartite q, g.map_selected q hq, ?_⟩
  exact hBase

/-- A selected PictureStep suffices to transport base coverage:
evaluate the picture-step property at any constant colouring to
obtain one actual selected transition. The homogeneity conclusion
is not needed for this invariant. -/
theorem PictureStep.coversBase
    {S T : ForestTailStage A B D family t targetTrain allowed}
    {α : UA ↪ P} {κ : Type w} [Nonempty κ]
    (h : PictureStep S T α κ) (hS : S.CoversBase) :
    T.CoversBase := by
  let colour :
      StructuralRamsey.Partite.ProjectedEmbedding A T.system α → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨g, _hg⟩ := h colour
  exact g.coversBase hS

/-- The OLD base-strongness condition of the checked source-transfer
theorems follows from the actual SELECTED strongness in the local
attachment specification, provided each base member has a selected
lift. This eliminates a previously unjustified stronger premise. -/
theorem ActiveAttachmentBounds.all_base_strong_of_covered
    {Y I : Type v}
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (e : Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)
    (bounds : ActiveAttachmentBounds stage hA e active E f U)
    (hCovered : stage.CoversBase) :
    ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b) := by
  intro b hb
  obtain ⟨q, hq, hBase⟩ := hCovered b hb
  rw [← hBase]
  exact bounds.baseStrong q hq

/-- The initial selected family contains one literal copy for every
prescribed base B-embedding; the witness is the checked initial
designated copy, with no new choice function or surjectivity axiom. -/
theorem initialForestStage_coversBase
    {S : ForestTailStage A B D family t targetTrain allowed}
    (hInitial : ∀ b : Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D S.system family,
        q ∈ S.selected ∧ q.base = b) :
    S.CoversBase := hInitial

end StructuralRamsey.Girth.TrainRecursiveWitness
