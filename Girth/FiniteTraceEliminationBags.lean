import Girth.FiniteTraceSimplicialCriterion
import Girth.FiniteTracePairGraph
import Mathlib.Data.Finset.Max

/-!
# The easy half of the clique-tree construction

Given a perfect elimination order, the bag at v consists of v and
all later neighbours of v.  Such a bag is a clique.  Every nonempty
clique is contained in the bag of its earliest vertex.

For the eventual tree construction, connect each v with a later
neighbour to its LEAST later neighbour. The elimination condition
ensures that every later vertex x occurring in the bag at v is
also in its parent's bag. Hence the vertex-occurrence sets are
connected along parent chains. Connect the component roots, then
delete contained or duplicate nonmaximal bags using the already
checked JoinTree.nonempty_eraseMember_of_full in
Girth/ForestTreeRewire.lean.

This file formalizes only the first two elementary facts. It does
NOT assume a perfect elimination ordering exists for an arbitrary
chordal graph, and it does not claim a global clique-tree theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The elimination bag of v: v itself and its later neighbours. -/
def laterNeighborBag
    [LinearOrder V] (G : SimpleGraph V) (v : V) : Set V :=
  {x | x = v ∨ (v < x ∧ G.Adj v x)}

/-- In a perfect elimination order, every elimination bag is a
clique. The equality case corresponds to the root vertex v. -/
theorem laterNeighborBag_isClique
    [LinearOrder V]
    (G : SimpleGraph V)
    (hPEO : IsPerfectEliminationOrder G)
    (v : V) :
    G.IsClique (laterNeighborBag G v) := by
  intro x hx y hy hxy
  rcases hx with hx | ⟨hvx, hvxAdj⟩
  · subst x
    rcases hy with hy | ⟨_, hvyAdj⟩
    · subst y
      exact (hxy rfl).elim
    · exact hvyAdj
  · rcases hy with hy | ⟨hvy, hvyAdj⟩
    · subst y
      exact hvxAdj.symm
    · exact hPEO v x y hvx hvy hxy hvxAdj hvyAdj

/-- Every nonempty clique is contained in the elimination bag
associated with its least vertex.  No chordality assumption is
needed beyond the given graph clique itself. -/
theorem clique_subset_laterNeighborBag_of_least
    [LinearOrder V]
    (G : SimpleGraph V)
    (K : Finset V) (hClique : G.IsClique (K : Set V))
    (v : V) (hv : v ∈ K)
    (hLeast : ∀ x ∈ K, v ≤ x) :
    (K : Set V) ⊆ laterNeighborBag G v := by
  intro x hx
  by_cases h : x = v
  · exact Or.inl h
  · have hNe : v ≠ x := fun he => h he.symm
    have hvx : v < x := lt_of_le_of_ne (hLeast x hx) hNe
    exact Or.inr ⟨hvx, hClique hv hx hNe⟩

/-- Every nonempty graph clique is contained in at least one
elimination bag, choosing its least vertex in the total order. -/
theorem clique_contained_in_some_laterNeighborBag
    [LinearOrder V]
    (G : SimpleGraph V) (K : Finset V)
    (hK : K.Nonempty)
    (hClique : G.IsClique (K : Set V)) :
    ∃ v : V, v ∈ K ∧
      (K : Set V) ⊆ laterNeighborBag G v := by
  classical
  let v : V := K.min' hK
  have hv : v ∈ K := Finset.min'_mem K hK
  have hLeast : ∀ x ∈ K, v ≤ x := by
    intro x hx
    exact Finset.min'_le K x hx
  exact ⟨v, hv,
    clique_subset_laterNeighborBag_of_least G K hClique v hv hLeast⟩

/-- Under a perfect elimination order, every nonempty maximal
graph clique is exactly the elimination bag at its least vertex.
Thus the elimination bags contain ALL maximal cliques (and may
also contain redundant nonmaximal or duplicate bags). -/
theorem maximalClique_eq_laterNeighborBag
    [LinearOrder V]
    (G : SimpleGraph V)
    (hPEO : IsPerfectEliminationOrder G)
    (K : Finset V) (hK : K.Nonempty)
    (hClique : G.IsClique (K : Set V))
    (hMax :
      ∀ L : Set V, (K : Set V) ⊆ L →
        G.IsClique L → L ⊆ (K : Set V)) :
    ∃ v : V, v ∈ K ∧
      (K : Set V) = laterNeighborBag G v := by
  obtain ⟨v, hv, hSub⟩ :=
    clique_contained_in_some_laterNeighborBag G K hK hClique
  have hBack : laterNeighborBag G v ⊆ (K : Set V) :=
    hMax (laterNeighborBag G v) hSub
      (laterNeighborBag_isClique G hPEO v)
  exact ⟨v, hv, Set.Subset.antisymm hSub hBack⟩


end StructuralRamsey.Girth
