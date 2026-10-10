import Girth.ForestAttach
import Girth.ForestSingleEdge

/-!
# Duplicated one-edge requests in a local forest

The manuscript's mixed forest property is stated for SETS of pieces.
A local request list may nevertheless name the same A-edge twice:
one selected A-copy and one separator request, or two neighbour
separator requests, can have exactly the same physical support edge.

This duplication is harmless ONLY for one-edge pieces. An arbitrary
B-piece cannot be freely duplicated, because a full B-support need
not be an allowed pairwise intersection. The theorem below attaches
a duplicate one-edge piece as a leaf to its original label.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Cloning a labelled ONE-EDGE member of a nonempty forest preserves
foresthood. The new copy is attached to its original label, not to
an arbitrary unrelated member. -/
theorem ForestOfCopies.append_duplicate_oneEdge
    [Fintype I] [Nonempty I]
    {F : I → HypergraphPiece W}
    (hForest : ForestOfCopies F)
    (p : I) (hOne : (F p).IsOneEdge) :
    ForestOfCopies
      (sumPieces F (fun _ : PUnit.{v+1} => F p)) := by
  have hCross : ∀ i : I, AllowedIntersection (F i) (F p) := by
    intro i
    by_cases hi : i = p
    · subst i
      right
      refine ⟨(F p).carrier, ?_, ?_, ?_⟩
      · rw [hOne]
        exact Set.mem_singleton _
      · rw [hOne]
        exact Set.mem_singleton _
      · exact Set.inter_self _
    · exact hForest.pairwiseAllowed hi
  apply forestOfCopies_attach_dominated
    hForest (F p) hCross p
  intro i x hx
  exact ⟨hx.1, hx.1⟩

end StructuralRamsey.Girth
