import Girth.FiniteTraceFinRotateCycle
import Girth.FiniteTraceTriangleCycle
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# A smaller induced-cycle certificate for Track 8

Instead of requiring a CrossPairNonedge witness for EVERY pair of
distinct cycle edges, it suffices to know that:
1. the consecutive 2-element edge sets are all distinct; and
2. the trace graph INDUCED on the cycle vertices is triangle-free.

These are standard properties of the Mathlib cycleGraph k for k>=4.
The remaining work is transporting an ordinary induced-cycle
embedding from cycleGraph k into the trace graph, together with
these two finite cycle-graph properties.  No such theorem is
postulated here.

The completed conclusion is precisely the contradiction required
by the manuscript's chordality proof; all added bags still come
from the original indexed cover.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- The bounded-original-cover cyclic obstruction, with its
nonadjacent cross-pair certificate derived rather than supplied. -/
theorem no_bounded_fin_cycle_of_triangleFree
    [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q k : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hk : 4 ≤ k)
    (hBudget : k ≤ q)
    (v : Fin k → Z)
    (hEdges :
      ∀ i : Fin k,
        (tracePairGraph F Z).Adj (v i) (v (finRotate k i)))
    (hDistinct :
      ∀ i j : Fin k, i ≠ j →
        ({v i, v (finRotate k i)} : Finset Z) ≠
          {v j, v (finRotate k j)})
    (hTriangleFree :
      ((tracePairGraph F Z).induce
        (pairPatternVertices v (fun i => v (finRotate k i)))).CliqueFree 3) :
    False := by
  apply no_bounded_chordless_fin_rotate
    F Z q k hLocal hk hBudget v hEdges
  intro i j hij
  exact crossPairNonedge_of_induced_cliqueFree
    (tracePairGraph F Z)
    v (fun e => v (finRotate k e))
    hEdges hDistinct hTriangleFree i j hij

end StructuralRamsey.Girth
