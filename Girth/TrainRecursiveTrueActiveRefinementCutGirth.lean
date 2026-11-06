import Girth.TrainRecursiveTrueActiveFirstCutGirth
import Girth.TrainRecursiveRefinementRetainedCutGirth
import Girth.TrainRecursiveParentChildCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# Genuine global inserted-cut girth for the active lower target

The previously missing first retained parent bound is obtained from the
old stage at level one, without inferring labelled girth from ordinary
bottom support girth.  The exact retained-level transport then moves
this bound across the actual FirstWagonRefinement; the global
parent-and-children induction descends through ALL new inserted cuts.

The first theorem uses the full shared old A-edge family.  The second
transfers the result to the exactly induced active relational A-support
by physical edge inclusion and injective vertex transport.  In both
theorems quotient labels are literal: different labels are NOT
identified merely because their carriers coincide.

Neither theorem asserts existence of the refinement, lower Ramsey
stage, or attached-output SupremeCycleBound.  Its genuine childGirth
certificates are explicit fields of the supplied refinement.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every inserted cut of the actual first-wagon refinement has GLOBAL
labelled girth beyond the lower head threshold, with all shared active
OLD A-edge labels retained. The only numerical inputs are
admissibility and head cutoff >2. -/
theorem ForestTailStage.trueActive_sharedInsertedCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (ht : Admissible t)
    (hm : 0 < t.length) (hq : 2 < t.headD 0)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩)
      (t.headD 0 - 1))
    (ρ : Fin (t.length + R.extraCuts + 1))
    (hρ : ρ.val ≤ R.extraCuts + 1) :
    LabelledGirthGT
      (R.train.wagonClassCarrier
        (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
        ρ) (t.headD 0 - 1) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let Tshared := stage.train.restrict
    (sharedOldACarrierInclusion A stage.system.toRelStructure S)
  let edge : SharedOldACarrierEdge A stage.system.toRelStructure S →
      Set stage.Vertex := fun a => a.1.1
  let first : Fin (t.length + 1) := ⟨1, by omega⟩
  have hOld :
      LabelledGirthGT
        (Tshared.wagonClassCarrier edge first) (t.headD 0) := by
    exact stage.trueActive_sharedFirstCutGirth e ht
  have hShift :
      EdgeTrainLevels.firstRefinementShift t.length R.extraCuts first =
        (⟨R.extraCuts + 1, by omega⟩ :
          Fin (t.length + R.extraCuts + 1)) := by
    apply Fin.ext
    change 1 + R.extraCuts = R.extraCuts + 1
    omega
  have hRetained :
      LabelledGirthGT
        (R.train.wagonClassCarrier edge
          (⟨R.extraCuts + 1, by omega⟩ :
            Fin (t.length + R.extraCuts + 1))) (t.headD 0 - 1) := by
    have hCut := R.labelledGirthGT_at_retained
      first (by change 0 < 1; omega) (t.headD 0) hOld
    rw [hShift] at hCut
    exact labelledGirthGT_mono hCut (by omega)
  exact R.labelledCutGirth_inserted_of_retained
    (by omega) hRetained ρ hρ

/-- The same global inserted-cut girth in the TRUE induced relational
active source, indexed by its complete, genuine physical A-support.
The vertex subtype inclusion is injective, so no cycle can appear. -/
theorem ForestTailStage.trueActive_inducedInsertedCutGirth
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (ht : Admissible t)
    (hm : 0 < t.length) (hq : 2 < t.headD 0)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      hm
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part
      (allowed ⟨1, Nat.succ_lt_succ hm⟩)
      (t.headD 0 - 1))
    (ρ : Fin (t.length + R.extraCuts + 1))
    (hρ : ρ.val ≤ R.extraCuts + 1) :
    LabelledGirthGT
      ((R.train.restrict
        (inducedACarrierToShared A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding))).wagonClassCarrier
        (fun edge : OldACarrierEdge A
          (stage.system.toRelStructure.induce
            (activeCarrier A stage.system e.toFunctionEmbedding)) => edge.1)
        ρ) (t.headD 0 - 1) := by
  exact trueActive_inducedCutGirth_of_shared A stage.system
    e.toFunctionEmbedding R.train ρ (t.headD 0 - 1)
    (stage.trueActive_sharedInsertedCutGirth e ht hm hq R ρ hρ)

end StructuralRamsey.Girth.TrainRecursiveWitness
