import Girth.TrainLabelledCutGirth
import Girth.TrainRecursivePhysicalCutTransfer
import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Honest labelled tail-cut girth of the true active induced source

The old ForestTailStage supplies FULL physical selected-system girth
at every positive TAIL coordinate. It implies horizontal girth of
the complete ambient quotient-labelled wagon cut.

The true active source retains exactly those A-edges inside the
actual active carrier. There are TWO different transports:
* restrict the edge labels from the whole picture to shared active
  edges, with injective wagon-class reindexing;
* move from shared ambient edges to the A-edges of the induced
  relational source, changing physical vertex type to the active
  subtype. Injectivity of subtype inclusion preserves labelled girth.

No edge is pruned from the AMBIENT picture; its actual active induced
substructure has genuinely fewer edges, as it should. In particular,
we do not identify different quotient wagon labels whose vertex
carriers coincide.

This settles the tail-cut transfer BEFORE inserting first-refinement
levels. It does NOT claim that local child-girth of the inserted
refinement gives global labelled cut-girth at its new positive levels.
-/

namespace StructuralRamsey.Girth

universe v
variable {W V I : Type v}

/-- Injective physical-vertex transport cannot introduce a short
labelled Berge cycle, even when the label type is unchanged and
carriers are only included in the images of the old carriers. -/
theorem labelledGirthGT_of_injective_vertex_map
    (f : V ↪ W) (old : I → Set W) (new : I → Set V)
    (hMaps : ∀ i : I, ∀ x : V, x ∈ new i → f x ∈ old i)
    (q : ℕ) (hOld : LabelledGirthGT old q) :
    LabelledGirthGT new q := by
  rintro ⟨cycle, hBound⟩
  let lifted : LabelledBergeCycle old := {
    length := cycle.length
    hlength := cycle.hlength
    label := cycle.label
    vertex := fun i => f (cycle.vertex i)
    label_injective := cycle.label_injective
    vertex_injective := by
      intro i j hij
      exact cycle.vertex_injective (f.injective hij)
    left_mem := fun i => hMaps (cycle.label i) (cycle.vertex i)
      (cycle.left_mem i)
    right_mem := fun i => hMaps (cycle.label (cyclicSucc i)) (cycle.vertex i)
      (cycle.right_mem i)
  }
  exact hOld ⟨lifted, hBound⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
open TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA P X : Type v}

/-- A labelled wagon-cut girth bound on actual SHARED OLD A-edges
transfers to the genuine induced active source and its own physical
A-edge labels. The exact induced support is used, not merely the
projected ambient A-edge subfamily. -/
theorem trueActive_inducedCutGirth_of_shared
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    {m : ℕ}
    (T : EdgeTrainLevels
      (SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C α)) m)
    (μ : Fin (m + 1)) (q : ℕ)
    (hShared : LabelledGirthGT
      (T.wagonClassCarrier (fun edge => edge.1.1) μ) q) :
    LabelledGirthGT
      ((T.restrict
        (inducedACarrierToShared A C.toRelStructure (activeCarrier A C α))).wagonClassCarrier
          (fun edge : OldACarrierEdge A
            (C.toRelStructure.induce (activeCarrier A C α)) => edge.1) μ) q := by
  let S := activeCarrier A C α
  let Source := C.toRelStructure.induce S
  let keep := inducedACarrierToShared A C.toRelStructure S
  let NewTrain := T.restrict keep
  let vertexMap : S ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  have hImage : LabelledGirthGT
      (NewTrain.wagonClassCarrier
        (fun edge : OldACarrierEdge A Source =>
          (Subtype.val : S → X) '' edge.1) μ) q := by
    apply T.labelledCutGirth_restrict
      (fun edge : SharedOldACarrierEdge A C.toRelStructure S => edge.1.1)
      keep
      (fun edge : OldACarrierEdge A Source =>
        (Subtype.val : S → X) '' edge.1)
      ?_ μ q hShared
    intro edge
    exact Set.Subset.rfl
  have hMaps (p : Quotient (NewTrain.wagonSetoid μ))
      (x : S) :
      x ∈ NewTrain.wagonClassCarrier
        (fun edge : OldACarrierEdge A Source => edge.1) μ p →
      vertexMap x ∈ NewTrain.wagonClassCarrier
        (fun edge : OldACarrierEdge A Source =>
          (Subtype.val : S → X) '' edge.1) μ p := by
    induction p using Quotient.inductionOn with
    | h edge =>
      change x ∈ NewTrain.wagonCarrier
          (fun edge : OldACarrierEdge A Source => edge.1) μ edge →
        x ∈ NewTrain.wagonCarrier
          (fun edge : OldACarrierEdge A Source =>
            (Subtype.val : S → X) '' edge.1) μ edge
      rintro ⟨f, hRel, hx⟩
      exact ⟨f, hRel, ⟨x, hx, rfl⟩⟩
  exact labelledGirthGT_of_injective_vertex_map vertexMap
    (NewTrain.wagonClassCarrier
      (fun edge : OldACarrierEdge A Source =>
        (Subtype.val : S → X) '' edge.1) μ)
    (NewTrain.wagonClassCarrier
      (fun edge : OldACarrierEdge A Source => edge.1) μ)
    hMaps q hImage

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every original positive TAIL cut of the old stage retains
its full labelled wagon-cut girth when restricted to all actual
shared A-edges in the true active fibre. -/
theorem ForestTailStage.trueActive_sharedTailCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (j : Fin t.length) (hj : 0 < j.val) :
    LabelledGirthGT
      ((stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
            (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
              (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
              j.castSucc) (t.get j) := by
  have hAmbient : LabelledGirthGT
      (stage.train.wagonClassCarrier (fun edge => edge.1) j.castSucc)
      (t.get j) :=
    selectedPicture_labelledCutGirth_of_fullSystemGirth
      A B D stage.system family stage.selected stage.train
      j.castSucc (t.get j) (stage.tailGirth j hj)
  exact stage.train.labelledCutGirth_restrict
    (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
    (sharedOldACarrierInclusion A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding))
    (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
    (fun _ => Set.Subset.rfl) j.castSucc (t.get j) hAmbient

/-- Consequently each old positive TAIL cut is valid in the exact
relational active-source train, with unchanged quotient labels
after both physical-edge and vertex restriction maps. -/
theorem ForestTailStage.trueActive_inducedTailCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (j : Fin t.length) (hj : 0 < j.val) :
    LabelledGirthGT
      (((stage.train.restrict
          (sharedOldACarrierInclusion A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding))).restrict
          (inducedACarrierToShared A stage.system.toRelStructure
            (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
          (fun edge : OldACarrierEdge A
            (stage.system.toRelStructure.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
          j.castSucc) (t.get j) := by
  exact trueActive_inducedCutGirth_of_shared A stage.system
    e.toFunctionEmbedding
    (stage.train.restrict
      (sharedOldACarrierInclusion A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding)))
    j.castSucc (t.get j)
    (stage.trueActive_sharedTailCutGirth e j hj)

end StructuralRamsey.Girth.TrainRecursiveWitness
