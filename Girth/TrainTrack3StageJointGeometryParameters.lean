import Girth.TrainTrack3JointGeometryParameters
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Numbered Track 3: the joint geometry/parameters output on a real forest stage

The actual recursive stage already stores the old physical A-support train,
its complete adjacent-part parameters, and original positive tail-girth
bounds. This wrapper does not request those fields a second time.

It is conditional on a genuine active projected A-copy and a local lower
witness with its own source parameters, exact interior train compatibility
and full system-girth at strictly interior cuts. No generated-output girth,
new selected-copy ownership, designated coverage or lower Ramsey witness
existence is assumed.

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

/-- Geometry and sibling-intersection parameters for a genuine nontrivial
recursive picture step, with the old source hypotheses taken directly from
its ForestTailStage fields. Both outputs use the entire actual A-support.
The witness system-girth input is on the ORIGINAL lower witness, never the
generated output. -/
theorem ForestTailStage.activeAttachment_joint_geometry_and_parameters_of_two_le_height
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (R : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) R)
    (U : EdgeTrainLevels (OldACarrierEdge A R.toRelStructure) t.length)
    (hHeight : 2 ≤ t.length)
    (hCoreParams : U.AdjacentParameters
      (fun edge : OldACarrierEdge A R.toRelStructure => edge.1)
      (fun ν => {y | R.part y ∈ allowed ν}))
    (hInterior : ∀ κ : Fin (t.length + 1), 0 < κ.val →
      κ.val < t.length →
      ∀ (i : I) (s r : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding)),
      stage.train.rel κ
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) s)
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) r) ↔
      U.rel κ
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)
          R.toRelStructure (fun i => (f i).toEmbedding) i s)
        (sharedOldACarrierCoreEmbedding A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)
          R.toRelStructure (fun i => (f i).toEmbedding) i r))
    (g : Fin (t.length + 1) → ℕ)
    (hg : ∀ μ : Fin (t.length + 1), 0 < μ.val →
      μ.val < t.length → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (t.length + 1), 0 < μ.val →
      μ.val < t.length →
      (activeGluingWitnessOrderOneData
        A stage.system e.toFunctionEmbedding R.toRelStructure
        (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT (g μ)) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let fRel := fun i => (f i).toEmbedding
    let hShared := activeCarrier_all_standard_copies_meet_core
      A stage.system e.toFunctionEmbedding active I
    let train := generatedActualASupportTrain
      A hA stage.system.toRelStructure S R.toRelStructure
      fRel stage.train U hShared
    let actual := RelStructure.Attachment.attach
      stage.system.toRelStructure S R.toRelStructure fRel
    (ALinear A actual ∧
      ∀ μ : Fin (t.length + 1),
        (attachedSelectedPictureOrderOneData A hA B D stage.system
          family stage.selected e R.toRelStructure fRel
          stage.train U hShared μ).LinearPretrain ∧
        ∀ W : Quotient (train.wagonSetoid μ),
          AStrong A actual
            (train.wagonClassCarrier
              (fun edge : OldACarrierEdge A actual => edge.1) μ W)) ∧
    train.AdjacentParameters
      (fun edge : ActualAttachedAEdge A stage.system.toRelStructure S
        R.toRelStructure fRel => edge.1)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach
          stage.system S R f).part x ∈ allowed ν}) := by
  have hOldCut : ∀ μ : Fin (t.length + 1), 0 < μ.val →
      μ.val < t.length →
      (selectedPictureOrderOneData A B D stage.system family
        stage.selected stage.train μ).LinearPretrain := by
    intro μ hPos hLt
    let j : Fin t.length := ⟨μ.val, hLt⟩
    have hCast : j.castSucc = μ := Fin.ext rfl
    have hOld := (stage.tailGirth j hPos).1
    exact Eq.mp (congrArg (fun ν : Fin (t.length + 1) =>
      (selectedPictureOrderOneData A B D stage.system family
        stage.selected stage.train ν).LinearPretrain) hCast) hOld
  exact track3_joint_geometry_and_parameters
    A hA B D stage.system family stage.selected e active R f
    stage.train U allowed stage.isPartite hBaseLinear hRigid hHeight
    hOldCut stage.parameters hCoreParams hInterior g hg hCoreCut


/-- At height one the original stage already carries old physical
A-linearity and old allowed-part sibling bounds.  Only the core's
linearity, the full-image strongness of its gluing maps, and its own
allowed-part parameters must be supplied.  There is no interior
train cut and no additional local system-girth coordinate. -/
theorem ForestTailStage.activeAttachment_joint_geometry_and_parameters_of_height_one
    {q : ℕ}
    (baseTrain : EdgeTrainLevels (OldACarrierEdge A B) 1)
    (permitted : Fin 2 → Set P)
    (stage : ForestTailStage A B D family [q] baseTrain permitted)
    (hA : A.Irreducible) (hBaseLinear : ALinear A D)
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (R : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) R)
    (U : EdgeTrainLevels (OldACarrierEdge A R.toRelStructure) 1)
    (hCoreLinear : ALinear A R.toRelStructure)
    (hImage : ∀ i : I, AStrong A R.toRelStructure
      (copyCarrier ((f i).toEmbedding)))
    (hCoreParams : U.AdjacentParameters
      (fun edge : OldACarrierEdge A R.toRelStructure => edge.1)
      (fun ν => {y | R.part y ∈ permitted ν})) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let fRel := fun i => (f i).toEmbedding
    let hShared := activeCarrier_all_standard_copies_meet_core
      A stage.system e.toFunctionEmbedding active I
    let train := generatedActualASupportTrain
      A hA stage.system.toRelStructure S R.toRelStructure
      fRel stage.train U hShared
    let actual := RelStructure.Attachment.attach
      stage.system.toRelStructure S R.toRelStructure fRel
    (ALinear A actual ∧
      ∀ μ : Fin 2,
        (attachedSelectedPictureOrderOneData A hA B D stage.system
          family stage.selected e R.toRelStructure fRel
          stage.train U hShared μ).LinearPretrain ∧
        ∀ W : Quotient (train.wagonSetoid μ),
          AStrong A actual
            (train.wagonClassCarrier
              (fun edge : OldACarrierEdge A actual => edge.1) μ W)) ∧
    train.AdjacentParameters
      (fun edge : ActualAttachedAEdge A stage.system.toRelStructure S
        R.toRelStructure fRel => edge.1)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach
          stage.system S R f).part x ∈ permitted ν}) := by
  exact track3_height_one_geometry_and_parameters
    A hA B D stage.system family stage.selected e active R f
    stage.train U permitted stage.isPartite hBaseLinear hRigid
    stage.aLinear hCoreLinear hImage stage.parameters hCoreParams

end StructuralRamsey.Girth.TrainRecursiveWitness
