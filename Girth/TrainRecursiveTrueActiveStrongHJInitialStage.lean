import Girth.TrainRecursiveTrueActiveInitialLowerStage
import Girth.TrainRecursiveStrongSupportedHJBase

set_option autoImplicit false
set_option Elab.async false

/-!
# A genuine strong Hales--Jewett base carries the lower initial forest stage

The previous initial lower-stage constructor accepts an arbitrary finite
A-partite larger base and a nonempty part-preserving family of target
embeddings. We remove those as independently selected inputs: the
already verified strong supported induced Hales--Jewett power supplies
the ACTUAL finite base, its genuine designated line family, strongness,
all-vertex physical support, and the literal partite Ramsey arrow.

The old ForestTailStage and its projected active A-copy supply the
genuine finite A-partite source, A-linearity, and physical support
coverage. Its true first-wagon refinement supplies the lower train.
The only separately assumed target geometry is the complete fine
AdjacentParameters and the exact-index positive labelled-cut girth,
whose independent proof candidates are #888 and merged #899.

This constructs an INITIAL lower ForestTailStage and a concrete
Hales--Jewett partite arrow, but NOT the full recursive lower Ramsey
witness, its selected-stage arrow after the picture pass, or the
attached-output SupremeCycleBound. No phantom high-girth assumption
is made about the Hales--Jewett power.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- From a real q>2 old stage and exact target-cut certificates,
construct the initial lower stage over the ACTUAL induced partite
Hales--Jewett base. Its prescribed family is the range of the
genuine partite line embeddings, with A-strong members and the
unrestricted partite Ramsey arrow at the chosen finite colour type.
There is no independent base, family, linearity or support premise. -/
theorem ForestTailStage.exists_initialLowerStage_over_strongHJBase
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
    (hFineParameters :
      (R.train.restrict
        (inducedACarrierToShared A₀.ordered stage.system.toRelStructure
          (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding))).AdjacentParameters
        (fun edge : OldACarrierEdge A₀.ordered
          (actualActiveSubsystemPartite A₀.ordered stage.system
            e.toFunctionEmbedding).toRelStructure => edge.1)
        (fun ρ =>
          (actualActiveSubsystemPartite A₀.ordered stage.system
            e.toFunctionEmbedding).part ⁻¹'
              (fineAllowedFromRefinement
                (q :: tail).length R.extraCuts
                (by simp : 0 < (q :: tail).length)
                e.toFunctionEmbedding allowed R.permitted ρ)))
    (hFineCuts :
      ∀ j : Fin ((q :: tail).length + R.extraCuts), 0 < j.val →
        LabelledGirthGT
          ((R.train.restrict
            (inducedACarrierToShared A₀.ordered stage.system.toRelStructure
              (activeCarrier A₀.ordered stage.system e.toFunctionEmbedding))).wagonClassCarrier
            (fun edge : OldACarrierEdge A₀.ordered
              (actualActiveSubsystemPartite A₀.ordered stage.system
                e.toFunctionEmbedding).toRelStructure => edge.1)
            j.castSucc)
          ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).get
            ⟨j.val, by
              simp only [List.length_append, List.length_replicate,
                List.length_cons]
              have hj := j.isLt
              simp only [List.length_cons] at hj
              omega⟩))
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
                  (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ρ))) := by
  classical
  let Source := actualActiveSubsystemPartite A₀.ordered stage.system
    e.toFunctionEmbedding
  let hSource : Source.IsPartiteOver A₀.ordered :=
    actualActiveSubsystemPartite_isPartiteOver A₀.ordered D
      stage.system stage.isPartite e
  letI : Finite stage.Vertex := stage.finiteVertex
  have hGeometry := ForestTailStage.trueActive_HJ_sourceGeometry
    A₀.ordered B D stage e
  have hIrreducible : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  obtain ⟨N, hN, hPartite, hLinear, hCover, lowerFamily,
      hNonempty, hParts, hStrong, hArrow⟩ :=
    exists_largeBase_strongSupportedHJLineRamseyFamily
      A₀ Source hSource hGeometry.2.1 hGeometry.2.2 κ
  letI : Nonempty lowerFamily := hNonempty
  have hInitial := stage.exists_initialLowerStage_of_activeTargetCuts
    hIrreducible e projected ht hq R
    (StructuralRamsey.Partite.Induced.power Source N)
    lowerFamily hParts hFineParameters hFineCuts
  exact ⟨N, hN, lowerFamily, hNonempty, hParts, hStrong, hArrow, hInitial⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
