import Girth.TrainRecursiveTrueActiveTailCutGirth
import Girth.TrainSystemCutGirthFullConverse
import Girth.TrainForestStageCoveredBottomReadyPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Same-vector F_t eligibility: induced active train has full wagon girth

F_t is applied to the TRUE induced active A-subsystem of the old
finite picture. It requires LABELLED wagon girth at the requested
q :: tail vector, not the stronger and generally nonhereditary
system-girth assertion for the active subsystem.

The old ForestTailStage already carries all POSITIVE-coordinate
FullSystemGirthGT bounds at their own cutoffs. The new BottomReady
field gives the bottom FullSystemGirthGT bound at q. The checked
full-system-to-labelled-wagon-girth theorem and injected restriction
of actual A-support labels transfer the bottom bound to the
true active induced train. The checked trueActive_inducedTailCutGirth
already transfers every positive proper coordinate.

No support edge is discarded except through the honest restriction
to the induced active vertex set; quotient wagon labels remain
faithfully injected, so the proof cannot collapse two labels merely
because their carrier sets coincide.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

variable (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
variable (e : Embedding A D)

local notation "S" => activeCarrier A stage.system e.toFunctionEmbedding
local notation "Bottom" =>
  (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))
local notation "SharedTrain" =>
  (stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S))
local notation "ActiveTrain" =>
  (SharedTrain.restrict
    (inducedACarrierToShared A stage.system.toRelStructure S))

/-- The first system-girth bound of the OLD actual picture restricts
to the same labelled wagon girth at bottom equality on the true
active induced support edge family. This is the EXACT q needed by F_t. -/
theorem ForestTailStage.trueActive_inducedBottomCutGirth
    (hBottom :
      (selectedPictureOrderOneData A B D stage.system family
        stage.selected stage.train Bottom).FullSystemGirthGT q) :
    LabelledGirthGT
      (ActiveTrain.wagonClassCarrier
        (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
          edge.1)
        Bottom) q := by
  have hAmbient : LabelledGirthGT
      (stage.train.wagonClassCarrier
        (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
        Bottom) q :=
    selectedPicture_labelledCutGirth_of_fullSystemGirth
      A B D stage.system family stage.selected stage.train
      Bottom q hBottom
  have hShared : LabelledGirthGT
      (SharedTrain.wagonClassCarrier
        (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
          edge.1.1) Bottom) q := by
    exact stage.train.labelledCutGirth_restrict
      (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (fun _ => Set.Subset.rfl) Bottom q hAmbient
  exact trueActive_inducedCutGirth_of_shared
    A stage.system e.toFunctionEmbedding
    SharedTrain Bottom q hShared

/-- The real induced active source carries the full labelled wagon
girth vector needed to invoke F_t at the SAME q :: tail cutoff.
Only old full system bounds are used: bottom from readiness and
positive coordinates from the existing ForestTailStage fields.
This is not a full-system bound on the active subsystem. -/
theorem ForestTailStage.trueActive_inducedSameVectorCutGirth
    (hReady : stage.BottomReady) :
    ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        (ActiveTrain.wagonClassCarrier
          (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
            edge.1)
          j.castSucc)
        ((q :: tail).get j) := by
  intro j
  by_cases hj : j.val = 0
  · have hIdx : j = (⟨0, by simp⟩ : Fin (q :: tail).length) :=
      Fin.ext hj
    subst j
    exact stage.trueActive_inducedBottomCutGirth e hReady
  · have hPos : 0 < j.val := by omega
    exact stage.trueActive_inducedTailCutGirth e j hPos

end StructuralRamsey.Girth.TrainRecursiveWitness
