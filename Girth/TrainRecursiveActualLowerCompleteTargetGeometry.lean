import Girth.TrainRecursiveTrueActiveTargetSupportData
import Girth.TrainRecursiveTrueActiveFineParameters
import Girth.TrainRecursiveTrueActiveLowerCutoffVector
import Girth.TrainRecursiveExactHeightTransport

set_option autoImplicit false
set_option Elab.async false

/-!
# Full fine-target geometry of the genuine active recursive source

For q>2, the lower recursive request has the literal cutoff vector
  replicate (R.extraCuts + 1) (q - 1) ++ tail.
The actual old stage and first-wagon refinement already prove:

* nonempty complete physical A-support and coverage of every active vertex;
* ordinary support girth at the exact new head cutoff q-1;
* adjacent fine parameters for every physical A-edge and every fine cut;
* all positive labelled horizontal-cut girths at the exact new list entries.

This theorem assembles those results AFTER transporting the physical train
along the genuine equality of heights. It changes no edge, support vertex,
selected-copy index or quotient-wagon relation. It is a TARGET theorem,
not a lower Ramsey picture pass or an output SupremeCycleBound.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
local notation "A" => A₀.ordered

/-- Exact lower target data, including FULL positive fine-cut girth.
No additional source girth, adjacent parameters, or nonempty support is
assumed beyond the genuine old stage and its supplied refinement. -/
theorem ForestTailStage.trueActive_completeLowerTargetGeometry
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding A
      stage.system e.toFunctionEmbedding)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A stage.system.toRelStructure
          (activeCarrier A stage.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding) => edge.1.1)
      stage.system.part (allowed ⟨1, by simp⟩) (q - 1))
    (hLen : (q :: tail).length + R.extraCuts =
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length) :
    let Target := actualActiveSubsystemPartite A stage.system
      e.toFunctionEmbedding
    let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
    let U := R.train.restrict
      (inducedACarrierToShared A stage.system.toRelStructure
        (activeCarrier A stage.system e.toFunctionEmbedding))
    let fineAllowed : Fin (lower.length + 1) → Set UA :=
      fun ρ => fineAllowedFromRefinement (q :: tail).length R.extraCuts
        (by simp : 0 < (q :: tail).length) e.toFunctionEmbedding
        allowed R.permitted
        (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ)
    Nonempty (OldACarrierEdge A Target.toRelStructure) ∧
      (∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
        ∃ edge : OldACarrierEdge A Target.toRelStructure,
          x ∈ edge.1) ∧
      GirthGT (supportCopies A Target.toRelStructure) (lower.headD 0) ∧
      (U.castHeight hLen).AdjacentParameters
        (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
        (fun ρ => Target.part ⁻¹' fineAllowed ρ) ∧
      (∀ j : Fin lower.length, 0 < j.val →
        LabelledGirthGT
          ((U.castHeight hLen).wagonClassCarrier
            (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
            j.castSucc)
          (lower.get j)) := by
  let Target := actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
  let lower := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
  let U := R.train.restrict
    (inducedACarrierToShared A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding))
  let fineAllowed : Fin (lower.length + 1) → Set UA :=
    fun ρ => fineAllowedFromRefinement (q :: tail).length R.extraCuts
      (by simp : 0 < (q :: tail).length) e.toFunctionEmbedding
      allowed R.permitted
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ)
  have hSource := stage.trueActive_initialSupportData e projected
    (q - 1) (by simp)
  have hHead : lower.headD 0 = q - 1 := by
    simp [lower, List.replicate_succ]
  have hParameters : (U.castHeight hLen).AdjacentParameters
      (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
      (fun ρ => Target.part ⁻¹' fineAllowed ρ) := by
    exact U.castHeight_adjacentParameters
      (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
      hLen
      (fun ρ =>
        Target.part ⁻¹' (fineAllowedFromRefinement
          (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length)
          e.toFunctionEmbedding allowed R.permitted ρ))
      (stage.trueActive_inducedRefinementAdjacentParameters
        e (by simp : 0 < (q :: tail).length) R)
  refine ⟨hSource.1, hSource.2.1, ?_, hParameters, ?_⟩
  · rw [hHead]
    exact hSource.2.2
  · intro j hj
    -- Dependent Fin indices must be CAST along hLen, not rewritten
    -- inside j.isLt: rewriting the bound changes the type of j.
    let jOld : Fin ((q :: tail).length + R.extraCuts) :=
      Fin.cast hLen.symm j
    have hPosOld : 0 < jOld.val := by
      simpa only [jOld, Fin.val_cast] using hj
    apply U.castHeight_labelledCutGirth
      (fun edge : OldACarrierEdge A Target.toRelStructure => edge.1)
      hLen j.castSucc (lower.get j)
    have hIdx :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm j.castSucc =
          jOld.castSucc := Fin.ext rfl
    rw [hIdx]
    simpa only [jOld, lower] using
      stage.trueActive_inducedAllLowerCutGirth e ht hq R jOld hPosOld

end StructuralRamsey.Girth.TrainRecursiveWitness
