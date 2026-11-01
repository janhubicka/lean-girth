import Girth.TrainBottomMixedForestGirth
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false

/-!
# Ordinary physical bottom girth is already part of the stage's forest invariant

The complete ForestTailStage bottom invariant tests every actual ambient
A-support edge as a genuine one-edge member.  Restrict its finite-set
mixed-forest assertion to these members and apply the generic distinct
one-edge forest-to-Berge-girth theorem. No extra bottom girth field is
needed for the recursive stage, nor any assumption of edge coverage by
selected B-copies.

This is a conditional property of an existing stage. It does not
construct the lower-rank stage, its tail supreme certificates or the
fine-train parameter geometry.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (family : Set (RelStructure.Embedding B D))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- An actual forest-tail stage has ordinary physical A-support girth
above its bottom forest cutoff. The finite mixed-family hypothesis
is applied to distinct one-edge members, not to noninjective labels. -/
theorem ForestTailStage.ordinaryBottomGirth
    (S : ForestTailStage A B D family t targetTrain allowed) :
    GirthGT (supportCopies A S.system.toRelStructure) (t.headD 0) := by
  apply girthGT_of_finiteOneEdgeForest
    (supportCopies A S.system.toRelStructure) (t.headD 0)
  intro s hTest hCard
  apply S.bottomForest s ?_ hCard
  intro F hF
  obtain ⟨edge, hEdge, hPiece⟩ := hTest F hF
  obtain ⟨a, ha⟩ := hEdge
  left
  refine ⟨a, ?_⟩
  have hOne : oneEdgePiece edge = HypergraphPiece.oneEdge edge := by
    rfl
  calc
    F = oneEdgePiece edge := hPiece
    _ = HypergraphPiece.oneEdge edge := hOne
    _ = HypergraphPiece.oneEdge (copyCarrier a) := by
      cases ha
      rfl

end StructuralRamsey.Girth.TrainRecursiveWitness
