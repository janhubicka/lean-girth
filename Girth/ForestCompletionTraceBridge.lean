import Girth.ForestActiveTraceGirth
import Girth.ForestCompletionProperty
import Girth.ForestCompletionSeparatorRequests

/-!
# From a genuine bounded forest-completion property to active girth

The revised girth paper uses the same bounded mixed forest-completion
invariant in two places: to construct the tree amalgam and to prove
that the A-support of the old active subsystem has high girth.

This module isolates the second implication. It uses the *existing*
ForestCompletionProperty and ForestCompletionWitness records, without
a new finite witness or an arbitrary-subfamily principle. The only
geometric inputs are:
  * full-edge or singleton traces of all tested members;
  * all designated extra members are tested;
  * every active edge is an ambient tested one-edge member;
  * active edges lie inside the active vertex carrier.

This candidate has not been Lean-compiled or axiom-audited yet.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- An actual finite mixed forest completion forces girth of the
linear active edge system, provided each allowed completed member
has a singleton/whole-edge trace on the active carrier.

This theorem retains exactly the completion predicate used by
the structural picture construction. The abstract trace-girth
theorem handles the first-occurrence/forest argument. -/
theorem girthGT_of_forestCompletion_smallOrWhole_trace
    (S : Set W) (H : Set (Set W)) (m : ℕ)
    (tested designated : HypergraphPiece W → Prop)
    (hComplete : ForestCompletionProperty tested designated m)
    (hLinear : LinearEdgeSet H)
    (hEdgeBig : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hEdgeSub : ∀ e : Set W, e ∈ H → e ⊆ S)
    (hTestEdge :
      ∀ e : Set W, e ∈ H →
        tested (HypergraphPiece.oneEdge e))
    (hBoundary :
      ∀ P : HypergraphPiece W, tested P →
        SmallOrWholeEdgeBoundary H S P)
    (hDesignatedTested :
      ∀ P : HypergraphPiece W, designated P → tested P) :
    GirthGT H m := by
  classical
  apply girthGT_of_bounded_smallOrWhole_forest_completions
    S H m hLinear hEdgeBig
  intro N finite edge hEdgeInj hEdges hCard
  letI : Fintype N := finite
  let selected : N → HypergraphPiece W :=
    fun n => HypergraphPiece.oneEdge (edge n)
  have hSelectedTest : ∀ n : N, tested (selected n) := by
    intro n
    exact hTestEdge (edge n) (hEdges n)
  obtain ⟨J, finiteJ, family, hWitness⟩ :=
    hComplete N selected hSelectedTest hCard
  refine ⟨J, finiteJ, family, hWitness.1, ?_, ?_⟩
  · intro j
    rcases hWitness.2.2 j with ⟨n, hEq⟩ | hDesignated
    · have hTest : tested (family j) := by
        rw [hEq]
        exact hSelectedTest n
      exact hBoundary (family j) hTest
    · exact hBoundary (family j)
        (hDesignatedTested (family j) hDesignated)
  · intro n
    obtain ⟨j, hEq⟩ := hWitness.2.1 n
    refine ⟨j, ?_⟩
    rw [hEq]
    change edge n ∩ S = edge n
    exact Set.inter_eq_left.mpr (hEdgeSub (edge n) (hEdges n))

end StructuralRamsey.Girth
