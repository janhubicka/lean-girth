import Girth.TrainRecursiveTrueActiveCoverage
import Girth.Berge

set_option autoImplicit false
set_option Elab.async false

/-!
# A-linearity of the true active target from the old physical forest bound

This is the missing direct input for using the actual Hales--Jewett
large Ramsey base in the q > 2 partite recursion. The lower active
source is not assumed A-linear: it inherits the full ambient physical
A-support girth from the old ForestTailStage, then girth > 2 forces
any two distinct physical A-copy carriers to meet in at most one vertex.

No selected edge is deleted; no new lower recursive witness,
positive fine full-system certificate, or output SupremeCycleBound
is constructed here. Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA X : Type v}

/-- Ordinary physical girth greater than two excludes two different
A-copy carriers sharing two vertices, even if an A-copy has several
different parametrizations. -/
theorem aLinear_of_supportGirth_two
    (A : RelStructure L UA) (R : RelStructure L X)
    (hGirth : GirthGT (supportCopies A R) 2) :
    ALinear A R := by
  intro e f hDifferent
  exact (pairwise_subsingleton_of_girthGT_two hGirth)
    (show copyCarrier e ∈ supportCopies A R from ⟨e, rfl⟩)
    (show copyCarrier f ∈ supportCopies A R from ⟨f, rfl⟩)
    hDifferent

end StructuralRamsey.Girth

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

/-- The old complete mixed bottom forest controls ALL ambient physical
A-copy carriers, so the true active induced source is A-linear.
No old designated-copy strongness or A-generation premise is needed. -/
theorem ForestTailStage.trueActive_aLinear
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (hq : 2 ≤ t.headD 0) :
    ALinear A
      (stage.system.toRelStructure.induce
        (activeCarrier A stage.system e.toFunctionEmbedding)) := by
  have hAmbient : GirthGT
      (supportCopies A stage.system.toRelStructure) (t.headD 0) := by
    apply girthGT_of_finiteMixedForestThrough _ _ (t.headD 0) stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  have hTwo : GirthGT
      (supportCopies A stage.system.toRelStructure) 2 :=
    girthGT_mono hAmbient hq
  have hActiveGirth : GirthGT
      (supportCopies A
        (stage.system.toRelStructure.induce
          (activeCarrier A stage.system e.toFunctionEmbedding))) 2 :=
    supportGirthGT_induce A stage.system.toRelStructure
      (activeCarrier A stage.system e.toFunctionEmbedding) 2 hTwo
  exact aLinear_of_supportGirth_two A
    (stage.system.toRelStructure.induce
      (activeCarrier A stage.system e.toFunctionEmbedding)) hActiveGirth

/-- The same unconditional conclusion, stated on the literal actual
A-partite source used by the recursive large-base construction. -/
theorem ForestTailStage.trueActivePartite_aLinear
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) (hq : 2 ≤ t.headD 0) :
    ALinear A
      (actualActiveSubsystemPartite A stage.system
        e.toFunctionEmbedding).toRelStructure :=
  stage.trueActive_aLinear e hq

end StructuralRamsey.Girth.TrainRecursiveWitness
