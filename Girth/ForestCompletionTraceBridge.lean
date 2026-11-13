import Girth.ForestActiveTraceGirth
import Girth.ForestCompletionProperty
import Girth.ForestCompletionSeparatorRequests

/-!
# From a genuine bounded forest-completion property to active girth

The revised girth paper uses the same bounded mixed forest-completion
invariant in two places: to construct the tree amalgam and to prove
that the A-support of the old active subsystem has high girth.

This module isolates the second implication using the existing
ForestCompletionProperty and ForestCompletionWitness records. The
selected pieces are already active one-edge members; their traces
need no further analysis. Only ADDED designated members require
whole-edge-or-singleton trace classification. This avoids both a
stronger boundary premise for all tested pieces and a new witness
construction.

This candidate has not been Lean-compiled or axiom-audited yet.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Exact trace reduction for the actual old active-girth argument.

The selected pieces are ONLY the active one-edge members. Their traces
are their own complete edges by the edge-containment hypothesis. The
forest completion adds ONLY designated B-support pieces; thus it is
enough to classify the traces of those added pieces. No trace premise
on arbitrary ambient A-copies or on every tested piece is required.
-/
theorem girthGT_of_forestCompletion_designated_traces
    (S : Set W) (H : Set (Set W)) (m : ℕ)
    (tested designated : HypergraphPiece W → Prop)
    (hComplete : ForestCompletionProperty tested designated m)
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hEdgeSub : ∀ e : Set W, e ∈ H → e ⊆ S)
    (hTestEdge :
      ∀ e : Set W, e ∈ H →
        tested (HypergraphPiece.oneEdge e))
    (hBoundaryDesignated :
      ∀ P : HypergraphPiece W, designated P →
        SmallOrWholeEdgeBoundary H S P) :
    GirthGT H m := by
  classical
  apply girthGT_of_bounded_smallOrWhole_forest_completions
    S H m hLinear hEdgeBig
  intro N finite edge _hEdgeInj hEdges hCard
  letI : Fintype N := finite
  let selected : N → HypergraphPiece W :=
    fun n => HypergraphPiece.oneEdge (edge n)
  have hSelectedTest : ∀ n : N, tested (selected n) := by
    intro n
    exact hTestEdge (edge n) (hEdges n)
  obtain ⟨J, finiteJ, family, hWitness⟩ :=
    hComplete N selected hSelectedTest hCard
  letI : Fintype J := finiteJ
  refine ⟨J, finiteJ, family, hWitness.1, ?_, ?_⟩
  · intro j
    rcases hWitness.2.2 j with ⟨n, hEq⟩ | hDesignated
    · rw [hEq]
      right
      refine ⟨edge n, hEdges n, ?_, ?_⟩
      · simp [selected, HypergraphPiece.oneEdge]
      · change edge n ∩ S = edge n
        exact Set.inter_eq_left.mpr
          (hEdgeSub (edge n) (hEdges n))
    · exact hBoundaryDesignated (family j) hDesignated
  · intro n
    obtain ⟨j, hEq⟩ := hWitness.2.1 n
    refine ⟨j, ?_⟩
    rw [hEq]
    change edge n ∩ S = edge n
    exact Set.inter_eq_left.mpr
      (hEdgeSub (edge n) (hEdges n))

end StructuralRamsey.Girth
