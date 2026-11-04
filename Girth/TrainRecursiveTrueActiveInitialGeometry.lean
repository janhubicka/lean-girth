import Girth.TrainRecursiveTrueActiveHJSource
import Girth.TrainRecursiveTrueActiveCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual q>2 lower initial target: inherited girth and genuine support

The recursive lower initial stage requires ordinary A-support girth at
its head cutoff, a nonempty physical A-edge, and coverage of every
target vertex by an actual A-support edge.

For the TRUE active subsystem (the actual induced relational source,
not all vertices of selected parts) these all follow from the OLD
ForestTailStage. The complete bottom mixed forest includes ALL ambient
A-edges; it implies ordinary girth in the old picture. Induced
restriction preserves that girth. A nonempty true active carrier
contains an actual projected A-copy and therefore has genuine
nonempty support. Every other active vertex is covered directly by
the definition of the active carrier.

This supplies intrinsic INPUT geometry for an actual lower initial
stage, with no independent lower-witness existence, no high-girth
claim about the Hales--Jewett power, and no output supreme-cycle
transfer.
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

/-- Complete ambient A-support girth of the TRUE active target inherits
any smaller numerical cutoff from the old stage's entire mixed bottom
forest. No part-fibre enlargement or A-edge pruning is used. -/
theorem ForestTailStage.trueActive_supportGirthGT
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (q : ℕ) (hq : q ≤ t.headD 0) :
    GirthGT
      (supportCopies A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure) q := by
  have hOld :
      GirthGT (supportCopies A stage.system.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (t.headD 0)
      stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  change GirthGT (supportCopies A
    (stage.system.toRelStructure.induce
      (activeCarrier A stage.system e.toFunctionEmbedding))) q
  exact supportGirthGT_induce A stage.system.toRelStructure
    (activeCarrier A stage.system e.toFunctionEmbedding) q
    (girthGT_mono hOld hq)

/-- Nonempty true active carrier yields a real physical A-edge INSIDE
the actual induced active source, not merely in its ambient picture. -/
theorem ForestTailStage.trueActive_supportNonempty
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (hActive : (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty) :
    Nonempty
      (OldACarrierEdge A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure) := by
  obtain ⟨s, ⟨a, rfl⟩⟩ :=
    actualRecursiveActiveSupport_nonempty A stage.system
      e.toFunctionEmbedding hActive
  exact ⟨actualEdge a⟩

/-- The complete intrinsic initial-target input geometry needed by
the lower recursive stage comes from the old actual stage: partiteness,
A-linearity, nonempty physical support, vertex support coverage and
ordinary support girth through any smaller head cutoff. -/
theorem ForestTailStage.trueActive_initialTargetGeometry
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (hActive : (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).IsPartiteOver A ∧
    ALinear A
      (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure ∧
    Nonempty
      (OldACarrierEdge A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure) ∧
    (∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
      ∃ a : Embedding A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure,
        x ∈ copyCarrier a) ∧
    GirthGT
      (supportCopies A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure) q := by
  obtain ⟨hPartite, hLinear, hCover⟩ :=
    stage.trueActive_HJ_sourceGeometry A B D e
  exact ⟨hPartite, hLinear,
    stage.trueActive_supportNonempty e hActive, hCover,
    stage.trueActive_supportGirthGT e q hq⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
