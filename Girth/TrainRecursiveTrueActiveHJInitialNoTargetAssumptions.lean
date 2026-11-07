import Girth.TrainRecursiveTrueActiveFineParameters
import Girth.TrainRecursiveTrueActiveStrongHJInitialStage
import Girth.TrainRecursiveTrueActiveLowerCutoffVector

set_option autoImplicit false
set_option Elab.async false

/-!
# Lower initial Hales--Jewett stage with all target geometry constructed

The old q>2 ForestTailStage, its genuine active A-copy, and its actual
FirstWagonRefinement R now supply the complete original source data.
Two separately validated bridges remove BOTH external lower target
geometry assumptions:

* complete fine AdjacentParameters, constructed from stage.parameters
  and genuine R.parameters with the canonical allowed A-parts;
* positive labelled cut girth at every literal lower-vector entry,
  including stronger retained tail thresholds.

The existing verified strong supported Hales--Jewett base supplies the
finite power, designated part-preserving A-strong line embeddings,
and the genuine partite Ramsey arrow. The verified initial-stage
constructor supplies the actual lower ForestTailStage on the exact
cast-height train, with ordinary support girth from bottomForest.

This is a deterministic-input CONSTRUCTION: it does not prove that the
lower recursive Ramsey picture PASS exists or that its selected output
satisfies the indexed SupremeCycleBound. Neither output is silently
assumed or asserted.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- All fine target geometry and the larger Hales--Jewett base are
constructed from the genuine old stage and refinement, with NO
extra fine girth or adjacent-parameter arguments. -/
theorem ForestTailStage.exists_initialLowerStage_over_strongHJBase_from_refinement
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB)
    (D : RelStructure L.withOrder P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : ForestTailStage A₀.ordered B D family (q :: tail)
      targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered stage.system e.toFunctionEmbedding)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (R : FirstWagonRefinement
      (stage.train.restrict
        (sharedOldACarrierInclusion A₀.ordered
          stage.system.toRelStructure
          (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A₀.ordered
        stage.system.toRelStructure
        (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding) =>
          edge.1.1)
      stage.system.part
      (allowed ⟨1, by simp⟩) (q - 1))
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    let Source := actualActiveSubsystemPartite A₀.ordered stage.system
      e.toFunctionEmbedding
    let hSource : Source.IsPartiteOver A₀.ordered :=
      actualActiveSubsystemPartite_isPartiteOver A₀.ordered D
        stage.system stage.isPartite e
    ∃ N : ℕ, 0 < N ∧
      let Large := StructuralRamsey.Partite.Induced.power Source N
      ∃ lowerFamily : Set (Embedding Source.toRelStructure Large.toRelStructure),
        Nonempty lowerFamily ∧
        (∀ b, b ∈ lowerFamily → ∀ x : activeCarrier
          A₀.ordered stage.system e.toFunctionEmbedding,
          Large.part (b x) = Source.part x) ∧
        (∀ b, b ∈ lowerFamily →
          AStrong A₀.ordered Large.toRelStructure (copyCarrier b)) ∧
        (∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) Large → κ,
          ∃ W : HalesJewett.Line
            (StructuralRamsey.Partite.Induced.Letter A₀.ordered Source) N,
            (StructuralRamsey.Partite.Induced.lineEmbedding hSource W).toEmbedding ∈
              lowerFamily ∧
            ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
                (StructuralRamsey.Partite.transversal A₀.ordered) Source,
              χ ((StructuralRamsey.Partite.Induced.lineEmbedding hSource W).comp a₁) =
                χ ((StructuralRamsey.Partite.Induced.lineEmbedding hSource W).comp a₂)) ∧
        ∃ hLen : (q :: tail).length + R.extraCuts =
            (List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length,
          Nonempty
            (ForestTailStage A₀.ordered Source.toRelStructure
              Large.toRelStructure lowerFamily
              (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
              ((R.train.restrict
                (inducedACarrierToShared A₀.ordered stage.system.toRelStructure
                  (activeCarrier A₀.ordered stage.system
                    e.toFunctionEmbedding))).castHeight hLen)
              (fun ρ => Large.part ⁻¹'
                (fineAllowedFromRefinement
                  (q :: tail).length R.extraCuts
                  (by simp : 0 < (q :: tail).length)
                  e.toFunctionEmbedding allowed R.permitted
                  (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ)))) := by
  have hParameters :=
    stage.trueActive_inducedRefinementAdjacentParameters e
      (by simp : 0 < (q :: tail).length) R
  have hCuts :=
    stage.trueActive_inducedAllLowerCutGirth e ht hq R
  exact ForestTailStage.exists_initialLowerStage_over_strongHJBase
    A₀ B D stage e projected ht hq R hParameters hCuts κ

end StructuralRamsey.Girth.TrainRecursiveWitness
