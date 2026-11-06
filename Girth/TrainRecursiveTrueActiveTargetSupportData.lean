import Girth.TrainRecursiveTrueActiveCoverage
import Girth.TrainRecursiveTrueActiveHJSource

set_option autoImplicit false
set_option Elab.async false

/-!
# The literal active target inherits complete physical support girth

A lower recursive forest stage must start from a target with actual
physical A-support girth, not merely A-linearity or a partite
projection. The OLD ForestTailStage.bottomForest controls every
ambient physical A-copy, and its full support girth passes to the
genuine induced active carrier without widening it to a part fibre.

This extracts the repeated argument from true-active coverage as an
independent reusable theorem for the lower initial stage. A second
statement packages its three physical support inputs: a real A-edge,
support of every true active vertex, and the requested girth.

Neither statement creates the lower Ramsey witness, asserts high
girth for an induced Hales--Jewett power, changes any designated
labels, or proves the attached output SupremeCycleBound. Circulation
only; no appendix.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- Every allowable cutoff of the OLD complete bottom forest gives
ordinary girth of ALL physical A-copy carriers in the actual true
active induced source. There is no selected-family restriction on
the support edges. -/
theorem ForestTailStage.trueActive_supportGirthGT
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (q : ℕ) (hq : q ≤ t.headD 0) :
    GirthGT (supportCopies A
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure) q := by
  have hAmbient : GirthGT
      (supportCopies A stage.system.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (t.headD 0)
      stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  change GirthGT
    (supportCopies A
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding))) q
  exact supportGirthGT_induce
    A stage.system.toRelStructure
    (activeCarrier A stage.system e.toFunctionEmbedding) q
    (girthGT_mono hAmbient hq)

/-- Three genuine inputs of the lower initial ForestTailStage, derived
from the OLD stage and one actual projected active A-copy: nonempty
physical support, full vertex coverage by A-edges, and support girth.
The source is literally the active A-partite induced subsystem. -/
theorem ForestTailStage.trueActive_initialSupportData
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A stage.system e.toFunctionEmbedding)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    Nonempty (OldACarrierEdge A
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure) ∧
    (∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
      ∃ edge : OldACarrierEdge A
        (actualActiveSubsystemPartite A stage.system
          e.toFunctionEmbedding).toRelStructure,
        x ∈ edge.1) ∧
    GirthGT (supportCopies A
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure) q := by
  have hSource :=
    ForestTailStage.trueActive_HJ_sourceGeometry A B D stage e
  refine ⟨?_, ?_, stage.trueActive_supportGirthGT e q hq⟩
  · let a := activeInduceProjected A projected
      (projected_mem_activeCarrier A stage.system
        e.toFunctionEmbedding projected)
    exact ⟨actualEdge a.val⟩
  · intro x
    obtain ⟨a, ha⟩ := hSource.2.2 x
    exact ⟨actualEdge a, ha⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
