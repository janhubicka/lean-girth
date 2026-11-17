import Girth.TrainCoverageFreePhysicalActiveWagonData
import Girth.TrainPhysicalPartiteForestData
import Girth.TrainRecursiveTrueActiveFineParameters
import Girth.TrainRecursiveTrueActiveTwoCopies
import Girth.TrainRecursiveExactHeightTransport
import Girth.TrainRecursiveTrueActiveFirstCutGirth
import Girth.TrainRefinementLowerCutGirth

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB} {D : RelStructure L P}
variable {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- A refinement of all the shared edges of the processed active subsystem. -/
abbrev firstRefinementAt
    (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) : Type v :=
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  FirstWagonRefinement
    (stage.train.restrict (sharedOldACarrierInclusion A stage.system.toRelStructure S))
    (by simp) (fun edge => edge.val.val) stage.system.part (allowed ⟨1, by simp⟩) (q - 1)

/-- The recursive input on the full true active support. Only the height
is reindexed to match the literal lower cutoff vector. -/
abbrev refinedActiveTrain
    (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) (R : firstRefinementAt stage e) :
    EdgeTrainLevels (OldACarrierEdge A
      (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure)
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length :=
  (R.train.restrict (inducedACarrierToShared A stage.system.toRelStructure
    (activeCarrier A stage.system e.toFunctionEmbedding))).castHeight
      (by simp only [List.length_append, List.length_replicate, List.length_cons]; omega)

/-- Pull back the permitted singleton parts and the retained parameters
along the processed base edge. -/
abbrev refinedActiveAllowed
    (stage : PhysicalForestStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D) (R : firstRefinementAt stage e) :
    Fin ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) → Set UA :=
  fun ν => fineAllowedFromRefinement (q :: tail).length R.extraCuts (by simp)
    e.toFunctionEmbedding allowed R.permitted
    (Fin.cast (by simp only [List.length_append, List.length_replicate, List.length_cons]; omega) ν)

/-- The active refinement has the exact labelled cut bounds and part
parameters of the smaller vector. All statements use the complete
active A-support. -/
theorem refinedActiveInput
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (R : firstRefinementAt stage e)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered stage.system
      e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
    : let Target := actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding
      let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
      let T := refinedActiveTrain stage e R
      (∀ (a : Embedding A₀.ordered Target.toRelStructure) x, Target.part (a x) = x) ∧
      (∀ x, ∃ a : Embedding A₀.ordered Target.toRelStructure, x ∈ copyCarrier a) ∧
      (∃ a b : Embedding A₀.ordered Target.toRelStructure, ¬ SameCopy a b) ∧
      T.AdjacentParameters (fun e => e.val) (fun ν => Target.part ⁻¹' refinedActiveAllowed stage e R ν) ∧
      (∀ j : Fin lower.length,
        LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.val) j.castSucc) (lower.get j)) := by
  let A := A₀.ordered
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let Shared := sharedOldACarrierInclusion A stage.system.toRelStructure S
  let Induced := inducedACarrierToShared A stage.system.toRelStructure S
  let Target := actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
  let m := (q :: tail).length
  have hm : 0 < m := Nat.zero_lt_succ _
  let g := q - 1
  let lower := List.replicate (R.extraCuts + 1) g ++ tail
  have hFine (a : Embedding A (Target).toRelStructure) (x : UA) : (Target).part (a x) = x :=
    actualActiveSubsystemPartite_fineEdges_of_projectedACopies A D stage.system
      stage.projectsACopies e (fun b h => ordered_embedding_eq_of_sameCopy b e h) a x
  have hSupport (x : S) : ∃ a : Embedding A (Target).toRelStructure, x ∈ copyCarrier a := by
    obtain ⟨edge, ⟨a, rfl⟩, hx⟩ := actualRecursiveActiveSupport_cover A stage.system
      e.toFunctionEmbedding x
    exact ⟨a, hx⟩
  have hTwo := activeTarget_twoGenuineCopies_of_nontrivialFibre A stage.system
    e.toFunctionEmbedding hPair
  let edge := fun a : SharedOldACarrierEdge A stage.system.toRelStructure S => a.1.1
  let T := stage.train.restrict Shared
  have hTail (j : Fin m) (hj : 0 < j.val) :
      LabelledGirthGT (T.wagonClassCarrier edge j.castSucc) ((q :: tail).get j) := by
    apply stage.train.labelledCutGirth_restrict (fun e => e.1) Shared edge
      (fun _ => Set.Subset.rfl) j.castSucc ((q :: tail).get j)
    exact selectedPicture_labelledCutGirth_of_fullSystemGirth A B D stage.system
      family stage.selected stage.train j.castSucc _ (stage.tailGirth j hj)
  have hFirst : LabelledGirthGT (T.wagonClassCarrier edge ⟨1, by simp⟩) g := by
    cases tail with
    | nil => exact T.top_labelledCutGirth edge g
    | cons r tail =>
        let j : Fin (q :: r :: tail).length := ⟨1, by simp⟩
        have hqj := ht.headD_le_get j
        exact labelledGirthGT_mono (hTail j (Nat.zero_lt_succ 0)) (by
          change q ≤ (q :: r :: tail).get j at hqj
          omega)
  have hLen : List.length lower = m + R.extraCuts := by
    simp only [lower, m, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hParameters := trueActive_inducedRefinementAdjacentParameters_of_parameters
    stage.system stage.train allowed stage.parameters e hm R
  have hCastParams := (R.train.restrict Induced).castHeight_adjacentParameters
    (fun edge => edge.1) hLen.symm
    (fun ν => (Target).part ⁻¹' fineAllowedFromRefinement m R.extraCuts hm
      e.toFunctionEmbedding allowed R.permitted ν) hParameters
  refine ⟨hFine, hSupport, hTwo, ?_, ?_⟩
  · with_unfolding_all exact hCastParams
  · intro j
    let k := Fin.cast hLen j
    have hShift : Fin.cast (congrArg (fun x : ℕ => x + 1) hLen.symm).symm j.castSucc =
        k.castSucc := Fin.ext rfl
    have hShared := refinedLabelledGirth_replicatedCutoffs (by omega : 2 ≤ g) R hFirst hTail k
    have hFine := trueActive_inducedCutGirth_of_shared A stage.system e.toFunctionEmbedding
      R.train k.castSucc ((lower).get j) (by simpa [k] using hShared)
    apply (R.train.restrict Induced).castHeight_labelledCutGirth
      (fun edge => edge.1) hLen.symm j.castSucc ((lower).get j)
    rw [hShift]
    exact hFine

/-- The active refinement has the exact lower vector's labelled cut bounds
and part parameters, so the lower forest assertion applies directly. -/
theorem exists_refinedActiveWitness
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (R : firstRefinementAt stage e)
    (ht : Admissible (q :: tail)) (hq : 2 < q) (κ : Type w)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered stage.system
      e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val)
    (hLower : FinePartiteForestAssertion A₀.ordered
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail) κ) :
    Nonempty (FinePartiteFtWitness A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding)
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      (refinedActiveTrain stage e R) (refinedActiveAllowed stage e R) κ) := by
  obtain ⟨hFine, hSupport, hTwo, hParams, hGirth⟩ :=
    refinedActiveInput A₀ stage e R ht hq hPair
  exact hLower (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding)
    (refinedActiveTrain stage e R) (refinedActiveAllowed stage e R)
    hFine hSupport hTwo hParams hGirth

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
