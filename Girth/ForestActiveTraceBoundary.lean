import Girth.ForestCompletionTraceBridge
import Girth.ForestRelationalBoundarySupport

/-!
# Actual A- and projected B-copy traces on the old active subsystem

Only the ADDED designated B-pieces need a geometric trace
classification. The selected A-edges are already whole active
edges and require no separate A-strongness lemma. A projected
B-copy meeting the active carrier in two vertices has exactly
one internal A-copy as boundary, belonging to its own complete
A-support.

The local edge-family membership is intentionally explicit so
that the corollaries can use the actual induced A-support rather
than a fabricated edge family. These are candidate source-level
adapters; no local Lean build was run.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- The base A-strongness hypothesis for a projected B-copy
identifies its actual whole-edge/vertex boundary on the old
active subsystem, provided every A-copy entirely within that
subsystem is listed in H. No independent ownership of a boundary
edge is assumed. -/
theorem projectedBCopy_smallOrWhole_activeBoundary
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b))
    (H : Set (Set X))
    (hActiveEdge :
      ∀ a : RelStructure.Embedding A C.toRelStructure,
        copyCarrier a ⊆ activeCarrier A C e.toFunctionEmbedding →
          copyCarrier a ∈ H) :
    SmallOrWholeEdgeBoundary H
      (activeCarrier A C e.toFunctionEmbedding)
      (embeddedACopySupportPiece A q.val) := by
  apply embeddedACopySupportPiece_smallOrWholeBoundary
    A q.val
    (activeCarrier A C e.toFunctionEmbedding) H
    (projectedCopy_activeCarrier_intersection_classify
      A B D C e b q hStrong)
  intro aB hEq
  apply hActiveEdge (q.val.comp aB)
  rw [← hEq]
  exact Set.inter_subset_right

end StructuralRamsey.Girth
