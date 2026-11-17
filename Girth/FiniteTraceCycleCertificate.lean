import Girth.FiniteTraceChordality
import Girth.FiniteTraceFinRotateCycle
import Girth.FiniteTraceTriangleCycle
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Finset.Image

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

/-- An induced-cycle witness has the exact two-sided adjacency
reflection required to transport the cycle graph's absence of
chords, as well as its distinctness of vertices. -/
theorem IsInducedFinCycle.adj_iff
    {U : Type v} (G : SimpleGraph U) (k : ℕ)
    (v : Fin k → U)
    (h : IsInducedFinCycle G k v)
    (i j : Fin k) :
    G.Adj (v i) (v j) ↔
      (SimpleGraph.cycleGraph k).Adj i j :=
  h.2 i j

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

/-- The union of the vertices of the successive indexed pairs
is precisely the range of the cyclic vertex map. -/
theorem pairPatternVertices_rotate_eq_range
    {U : Type v} (k : ℕ) (v : Fin k → U) :
    pairPatternVertices v (fun i => v (finRotate k i)) =
      Set.range v := by
  ext x
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, h.symm⟩
    · exact ⟨finRotate k i, h.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Or.inl hi.symm⟩

/-- An induced-cycle embedding transfers the absence of
triangles from the standard finite cycle graph to the graph
induced on its image. Adjacency reflection, not just
edge-preservation, is essential here. -/
theorem IsInducedFinCycle.image_cliqueFree_three
    {U : Type v} (G : SimpleGraph U) (k : ℕ)
    (v : Fin k → U)
    (h : IsInducedFinCycle G k v)
    (hFree : (SimpleGraph.cycleGraph k).CliqueFree 3) :
    (G.induce (Set.range v)).CliqueFree 3 := by
  classical
  intro S hClique
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    ((G.induce (Set.range v)).is3Clique_iff).mp hClique
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨j, hj⟩ := y.2
  obtain ⟨l, hl⟩ := z.2
  have hij : (SimpleGraph.cycleGraph k).Adj i j := by
    apply (h.2 i j).mp
    have hxyG : G.Adj x.1 y.1 := hxy
    simpa only [hi, hj] using hxyG
  have hil : (SimpleGraph.cycleGraph k).Adj i l := by
    apply (h.2 i l).mp
    have hxzG : G.Adj x.1 z.1 := hxz
    simpa only [hi, hl] using hxzG
  have hjl : (SimpleGraph.cycleGraph k).Adj j l := by
    apply (h.2 j l).mp
    have hyzG : G.Adj y.1 z.1 := hyz
    simpa only [hj, hl] using hyzG
  have hTriangle :
      (SimpleGraph.cycleGraph k).IsNClique 3
        ({i, j, l} : Finset (Fin k)) :=
    ((SimpleGraph.cycleGraph k).is3Clique_triple_iff).mpr
      ⟨hij, hil, hjl⟩
  exact hFree _ hTriangle

/-- Injectivity of the vertex map preserves the distinction
between different unordered consecutive pairs. -/
theorem IsInducedFinCycle.image_distinct_edges
    {U : Type v} (G : SimpleGraph U) (k : ℕ)
    (v : Fin k → U)
    (h : IsInducedFinCycle G k v)
    (hIndices :
      ∀ i j : Fin k, i ≠ j →
        ({i, finRotate k i} : Finset (Fin k)) ≠
          {j, finRotate k j}) :
    ∀ i j : Fin k, i ≠ j →
      ({v i, v (finRotate k i)} : Finset U) ≠
        {v j, v (finRotate k j)} := by
  classical
  intro i j hij hImageEq
  have hImageSets :
      ({i, finRotate k i} : Finset (Fin k)).image v =
        ({j, finRotate k j} : Finset (Fin k)).image v := by
    simpa only [Finset.image_insert, Finset.image_singleton]
      using hImageEq
  exact hIndices i j hij
    ((Finset.image_injective h.1) hImageSets)

/-- Precise induced-cycle obstruction conditional ONLY on three
standard properties of the pinned Mathlib cycleGraph:
successor edges, distinct unordered successor edges, and absence
of triangles at length >=4. None is assumed for the ambient graph.
Ordinary graph embeddings lacking adjacency reflection are rejected. -/
theorem no_bounded_induced_fin_cycle_of_standard_cycle_facts
    [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q k : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hk : 4 ≤ k) (hBudget : k ≤ q)
    (v : Fin k → Z)
    (hInduced :
      IsInducedFinCycle (tracePairGraph F Z) k v)
    (hCycleEdges :
      ∀ i : Fin k,
        (SimpleGraph.cycleGraph k).Adj i (finRotate k i))
    (hCycleDistinct :
      ∀ i j : Fin k, i ≠ j →
        ({i, finRotate k i} : Finset (Fin k)) ≠
          {j, finRotate k j})
    (hCycleTriangleFree :
      (SimpleGraph.cycleGraph k).CliqueFree 3) :
    False := by
  have hEdges :
      ∀ i : Fin k,
        (tracePairGraph F Z).Adj (v i)
          (v (finRotate k i)) := by
    intro i
    exact (hInduced.2 i (finRotate k i)).mpr
      (hCycleEdges i)
  have hDistinct :=
    IsInducedFinCycle.image_distinct_edges
      (tracePairGraph F Z) k v hInduced hCycleDistinct
  have hFree :
      ((tracePairGraph F Z).induce
        (pairPatternVertices v
          (fun i => v (finRotate k i)))).CliqueFree 3 := by
    rw [pairPatternVertices_rotate_eq_range]
    exact IsInducedFinCycle.image_cliqueFree_three
      (tracePairGraph F Z) k v hInduced hCycleTriangleFree
  exact no_bounded_fin_cycle_of_triangleFree
    F Z q k hLocal hk hBudget v hEdges hDistinct hFree


end StructuralRamsey.Girth
