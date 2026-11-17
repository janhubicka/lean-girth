import Girth.TrainCoverageFreePhysicalOrderPass
import Girth.TrainCoverageFreePhysicalActiveWagonData
import Girth.TrainRecursiveTrueActiveTailCutGirth
import Girth.TrainSystemCutGirthFullConverse
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Real coverage-free F_t eligibility: all induced active labelled cuts

The standalone forest-to-order pass cannot use the checked
ForestTailStage.trueActive_inducedTailCutGirth directly, because
its stronger recursive stage carries an extra mixedCoverage proof
which the circulation F_t assertion NEVER supplies.

The actual physical restriction lemmas used in that theorem DO
NOT mention mixedCoverage. Use them once in a generic cut lemma:
  full selected ORIGINAL system girth >g
    => full ambient LABELLED wagon girth >g
    => labelled girth of shared physical A-edges >g
    => labelled girth of the TRUE induced active A-support train >g.

The second restriction is across the injective physical vertex
inclusion; quotient wagon labels remain distinct. A complete
ambient edge is deleted only if it is not contained in the true
active source, not merely because it is unselected.

The bottom readiness gives the first cutoff q. Every positive
proper coordinate is already a field of CoverageFree.PhysicalForestStage.
The resulting active train satisfies EXACTLY the SAME q::tail
labelled wagon-girth vector required by F_t. No active full-system
girth hypothesis and no mixed irreducible coverage.
-/

/-!
Local labelled wagon girth from the original physical stage's
full system-girth bounds. This proof never used full IsPartiteOver,
so it transfers literally to PhysicalForestStage. Uncompiled.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

variable (stage : PhysicalForestStage A B D family
  (q :: tail) targetTrain allowed)
variable (e : Embedding A D)

local notation "S" =>
  activeCarrier A stage.system e.toFunctionEmbedding

/-- Any exact full-system bound on the ORIGINAL coverage-free picture
passes to labelled horizontal girth of the true induced active
source at the SAME cut. This lemma works for every cut, so bottom
and positive coordinates require no separate proofs. -/
theorem PhysicalForestStage.trueActive_cutGirth_of_fullSystem
    (μ : Fin ((q :: tail).length + 1)) (g : ℕ)
    (hFull :
      (selectedPictureOrderOneData A B D stage.system family
        stage.selected stage.train μ).FullSystemGirthGT g) :
    LabelledGirthGT
      ((stage.activeFineTrain e).wagonClassCarrier
        (fun edge : OldACarrierEdge A
          (stage.system.toRelStructure.induce S) => edge.1) μ) g := by
  let sharedTrain := stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
  have hAmbient : LabelledGirthGT
      (stage.train.wagonClassCarrier
        (fun edge : OldACarrierEdge A stage.system.toRelStructure =>
          edge.1) μ) g :=
    selectedPicture_labelledCutGirth_of_fullSystemGirth
      A B D stage.system family stage.selected
      stage.train μ g hFull
  have hShared : LabelledGirthGT
      (sharedTrain.wagonClassCarrier
        (fun edge : SharedOldACarrierEdge
          A stage.system.toRelStructure S => edge.1.1) μ) g :=
    stage.train.labelledCutGirth_restrict
      (fun edge : OldACarrierEdge A
        stage.system.toRelStructure => edge.1)
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)
      (fun edge : SharedOldACarrierEdge A
        stage.system.toRelStructure S => edge.1.1)
      (fun _ => Set.Subset.rfl) μ g hAmbient
  exact trueActive_inducedCutGirth_of_shared
    A stage.system e.toFunctionEmbedding
    sharedTrain μ g hShared

/-- The genuine active F_t source inherits labelled wagon girth
at EXACTLY q::tail, requiring only the old stage's bottom
system-girth readiness and its already stored positive bounds.
In particular the q=2 case is not excluded. -/
theorem PhysicalForestStage.trueActive_sameVectorCutGirth
    (hBottom : stage.BottomReady) :
    ∀ j : Fin (q :: tail).length,
      LabelledGirthGT
        ((stage.activeFineTrain e).wagonClassCarrier
          (fun edge : OldACarrierEdge A
            (stage.system.toRelStructure.induce S) => edge.1)
          j.castSucc)
        ((q :: tail).get j) := by
  intro j
  by_cases hj : j.val = 0
  · have hJ : j =
        (⟨0, by simp⟩ : Fin (q :: tail).length) :=
      Fin.ext hj
    subst j
    exact PhysicalForestStage.trueActive_cutGirth_of_fullSystem stage e
      (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))
      q hBottom
  · have hPositive : 0 < j.val := by omega
    exact PhysicalForestStage.trueActive_cutGirth_of_fullSystem stage e
      j.castSucc ((q :: tail).get j)
      (stage.tailGirth j hPositive)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
