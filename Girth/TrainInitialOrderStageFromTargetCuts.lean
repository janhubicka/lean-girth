import Girth.TrainForestStageBottomReadyPass
import Girth.TrainRecursiveWitnessInitialStage
import Girth.TrainRecursiveInitialTailSystem
import Girth.LinearityGirthTwo
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual initial OrderStage from the target's labelled wagon bounds

The disjoint initial picture is already built as ForestTailStage
from target support girth, target train parameters and coverage.
The only older source field supplied independently in that
constructor was initial tail system girth.

The checked theorem initialTrain_fullSystemGirth_of_targetCut
derives full initial system girth at EVERY proper cut from the
target's natural LABELLED horizontal wagon girth at the same
cutoff. The same theorem gives bottom full girth as well, so
the new bottom readiness predicate is satisfied initially.

There is no need to assume an initial output system-girth bound,
a local forest witness, an arrow or a future recursive stage.
This is the initial data at the SAME input cutoff vector.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- An actual finite initial selected OrderStage from the INPUT
target's own labelled wagon girth, ordinary A-support girth and
original adjacent part parameters. The initial disjoint selected
copies, whole physical train and target restriction remain literal.
Every proper coordinate has its own cutoff; no common weakening. -/
noncomputable def initialOrderStage_of_allTargetCuts
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (q : ℕ) (tail : List ℕ)
    (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length)
    (allowed : Fin ((q :: tail).length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) q)
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hCutoff : ∀ j : Fin (q :: tail).length,
      2 ≤ (q :: tail).get j)
    (hTargetCut : ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j)) :
    OrderStage A B D family (q :: tail) targetTrain allowed := by
  letI : Nonempty VB := by
    obtain ⟨edge⟩ := hSupportNonempty
    obtain ⟨a, _⟩ := edge.2
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨a u⟩
  have hTargetLinear : ALinear A B :=
    aLinear_of_girthGT_two A B
      (girthGT_mono hGirth (by
        simpa using hCutoff (⟨0, by simp⟩ : Fin (q :: tail).length)))
  have hm : 0 < (q :: tail).length := by simp
  have hAt (j : Fin (q :: tail).length) :
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B
          (fun b : family => b.1.toFunctionEmbedding)
          targetTrain hm) j.castSucc).FullSystemGirthGT ((q :: tail).get j) :=
    initialTrain_fullSystemGirth_of_targetCut
      A hA B D family targetTrain hm
      j.castSucc (by simpa using j.isLt)
      ((q :: tail).get j) (hCutoff j) hTargetLinear (hTargetCut j)
  let stage := initialForestTailStage_of_tail
    A hA B D family (q :: tail) ht targetTrain allowed
    hSupportNonempty hSupportCovers hGirth hTargetParameters
    (fun j _hj => hAt j)
  have hBottom :
      (selectedPictureOrderOneData A B D stage.system family stage.selected
        stage.train
        (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q := by
    simpa using hAt (⟨0, by simp⟩ : Fin (q :: tail).length)
  exact stage.withBottomSystemGirth hBottom

end StructuralRamsey.Girth.TrainRecursiveWitness
