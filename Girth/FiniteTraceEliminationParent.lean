import Girth.FiniteTraceEliminationBags

/-!
# Parent inclusion for perfect-elimination clique bags

Given a perfect elimination ordering, choose at each vertex v
having a later neighbour the least later neighbour p(v). Every
other later neighbour x of v belongs to the clique bag of p(v):
either x = p(v), or x is a later neighbour of p(v), since all
later neighbours of v form a clique.

This is the exact local inclusion that ensures running
intersection in the usual elimination-tree construction.
Constructing the whole tree and deleting nonmaximal bags
remain separate steps.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The finite set of neighbours later than v in a given total order. -/
noncomputable def laterNeighbors
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => v < x ∧ G.Adj v x

/-- Membership in the later-neighbour finset has its intended meaning. -/
theorem mem_laterNeighbors_iff
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (v x : V) :
    x ∈ laterNeighbors G v ↔ v < x ∧ G.Adj v x := by
  classical
  simp [laterNeighbors]

/-- The chosen parent is later than the vertex and adjacent to it. -/
theorem min_laterNeighbor_specs
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (v : V)
    (hN : (laterNeighbors G v).Nonempty) :
    v < (laterNeighbors G v).min' hN ∧
      G.Adj v ((laterNeighbors G v).min' hN) :=
  (mem_laterNeighbors_iff G v _).mp
    (Finset.min'_mem (laterNeighbors G v) hN)

/-- The least later neighbour of v is no larger than every other
later neighbour of v. -/
theorem min_laterNeighbor_le
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (v x : V)
    (hN : (laterNeighbors G v).Nonempty)
    (hvx : v < x) (hAdj : G.Adj v x) :
    (laterNeighbors G v).min' hN ≤ x :=
  Finset.min'_le (laterNeighbors G v) x
    ((mem_laterNeighbors_iff G v x).mpr ⟨hvx, hAdj⟩)

/-- Every later neighbour x of v lies in the parent bag, not
just in the bag of v.  This is the running-intersection
transfer along one parent edge. -/
theorem laterNeighbor_mem_parentBag
    [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hPEO : IsPerfectEliminationOrder G)
    (v x : V)
    (hN : (laterNeighbors G v).Nonempty)
    (hvx : v < x) (hAdj : G.Adj v x) :
    x ∈ laterNeighborBag G ((laterNeighbors G v).min' hN) := by
  let p : V := (laterNeighbors G v).min' hN
  have hVp : v < p := (min_laterNeighbor_specs G v hN).1
  have hvpAdj : G.Adj v p := (min_laterNeighbor_specs G v hN).2
  have hpx : p ≤ x :=
    min_laterNeighbor_le G v x hN hvx hAdj
  by_cases hEq : x = p
  · exact Or.inl hEq
  · have hLess : p < x := lt_of_le_of_ne hpx hEq.symm
    have hpAdj : G.Adj p x :=
      hPEO v p x hVp hvx hEq.symm hvpAdj hAdj
    exact Or.inr ⟨hLess, hpAdj⟩

end StructuralRamsey.Girth
