import Girth.TrainSelectedPictureIntrinsicGeometry
import Girth.TrainRecursiveWitnessPass

set_option Elab.async false

/-!
# Actual recursive-stage input to generated-wagon geometry

The finite recursive pass already stores partiteness, physical A-linearity,
and full tail system-girth in `ForestTailStage`.  Its interior old-cut
linearity need not be supplied again.  This theorem consumes those fields
directly and applies the intrinsic generated-wagon theorem to one genuine
active fibre.

It establishes all output cut linearity and complete wagon strongness,
including both endpoint cuts.  The general interface retains physical
core A-linearity and whole gluing-image strongness to cover heights with
no interior cut.  At height at least two, these follow from the first
interior witness bound; only actual interior train compatibility and
intrinsic witness system-girth remain as local inputs.  Neither the local
Ramsey witness nor the output tail system-girth is asserted by this
geometric assembly.  Constructing the full next `ForestTailStage` still
requires its separate forest, selected-copy, and cycle-transfer data.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (RelStructure.Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The geometric part of a recursive active picture step follows from
the genuine old stage invariant and the intrinsic local witness.  No old
strongness or all-level relation premise is repeated, and no cycle bound
is requested at the bottom or universal top. -/
theorem ForestTailStage.activeAttachment_allLevels_linear_and_strong
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) R)
    (U : EdgeTrainLevels (OldACarrierEdge A R) t.length)
    (hCoreLinear : ALinear A R)
    (hImage : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (hInterior : ∀ (μ : Fin (t.length + 1)), 0 < μ.val → μ.val < t.length →
      ∀ (i : I) (p q : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding)),
      stage.train.rel μ p.1 q.1 ↔
        U.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding) R f i p)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding) R f i q))
    (g : Fin (t.length + 1) → ℕ)
    (hg : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding R f U μ).FullSystemGirthGT (g μ)) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let hShared := activeCarrier_all_standard_copies_meet_core
      A stage.system e.toFunctionEmbedding active I
    let train := generatedActualASupportTrain
      A hA stage.system.toRelStructure S R f stage.train U hShared
    let actual := RelStructure.Attachment.attach stage.system.toRelStructure S R f
    ALinear A actual ∧
      ∀ μ : Fin (t.length + 1),
        (attachedSelectedPictureOrderOneData A hA B D stage.system family
          stage.selected e R f stage.train U hShared μ).LinearPretrain ∧
        ∀ W : Quotient (train.wagonSetoid μ),
          AStrong A actual
            (train.wagonClassCarrier (fun edge : OldACarrierEdge A actual => edge.1) μ W) := by
  apply attachedSelectedPicture_allLevels_linear_and_strong_of_intrinsic
    A hA B D stage.system family stage.selected e active R f stage.train U hInterior
    stage.isPartite hBaseLinear hRigid stage.aLinear hCoreLinear
    ?_ g hg hCoreCut hImage
  intro μ hPos hLt
  let j : Fin t.length := ⟨μ.val, hLt⟩
  have hCast : j.castSucc = μ := Fin.ext rfl
  have hOld := (stage.tailGirth j hPos).1
  exact Eq.mp (congrArg (fun ν : Fin (t.length + 1) =>
    (selectedPictureOrderOneData A B D stage.system family stage.selected
      stage.train ν).LinearPretrain) hCast) hOld

/-- With a genuine interior cut, the old stage and local witness bounds
already supply source physical linearity and whole gluing-image
strongness.  Thus the recursive geometric step requires no separate
core-linearity or gluing-strongness input, and still no endpoint bound. -/
theorem ForestTailStage.activeAttachment_allLevels_linear_and_strong_of_two_le_height
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A stage.system e.toFunctionEmbedding)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) R)
    (U : EdgeTrainLevels (OldACarrierEdge A R) t.length)
    (hHeight : 2 ≤ t.length)
    (hInterior : ∀ (μ : Fin (t.length + 1)), 0 < μ.val → μ.val < t.length →
      ∀ (i : I) (p q : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding)),
      stage.train.rel μ p.1 q.1 ↔
        U.rel μ
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding) R f i p)
          (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding) R f i q))
    (g : Fin (t.length + 1) → ℕ)
    (hg : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (t.length + 1), 0 < μ.val → μ.val < t.length →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding R f U μ).FullSystemGirthGT (g μ)) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let hShared := activeCarrier_all_standard_copies_meet_core
      A stage.system e.toFunctionEmbedding active I
    let train := generatedActualASupportTrain
      A hA stage.system.toRelStructure S R f stage.train U hShared
    let actual := RelStructure.Attachment.attach stage.system.toRelStructure S R f
    ALinear A actual ∧
      ∀ μ : Fin (t.length + 1),
        (attachedSelectedPictureOrderOneData A hA B D stage.system family
          stage.selected e R f stage.train U hShared μ).LinearPretrain ∧
        ∀ W : Quotient (train.wagonSetoid μ),
          AStrong A actual
            (train.wagonClassCarrier (fun edge : OldACarrierEdge A actual => edge.1) μ W) := by
  apply attachedSelectedPicture_allLevels_linear_and_strong_of_two_le_height
    A hA B D stage.system family stage.selected e active R f stage.train U hInterior
    stage.isPartite hBaseLinear hRigid hHeight
    ?_ g hg hCoreCut
  intro μ hPos hLt
  let j : Fin t.length := ⟨μ.val, hLt⟩
  have hCast : j.castSucc = μ := Fin.ext rfl
  have hOld := (stage.tailGirth j hPos).1
  exact Eq.mp (congrArg (fun ν : Fin (t.length + 1) =>
    (selectedPictureOrderOneData A B D stage.system family stage.selected
      stage.train ν).LinearPretrain) hCast) hOld

end StructuralRamsey.Girth.TrainRecursiveWitness
