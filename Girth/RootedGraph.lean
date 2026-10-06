import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # Rooting ordinary trees

Generic rooted-tree utilities for SimpleGraph.IsTree. The girth formalization
previously carried the same arguments only for join trees; these lemmas make
the graph-theoretic core reusable by the incidence-contraction argument.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

namespace SimpleGraph

/-- The unique root-to-vertex path in a tree. -/
noncomputable def IsTree.rootPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) :
    G.Walk root v :=
  Classical.choose (hG.existsUnique_path root v)

theorem IsTree.rootPath_isPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) :
    (hG.rootPath root v).IsPath :=
  (Classical.choose_spec (hG.existsUnique_path root v)).1

theorem IsTree.rootPath_unique
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (p : G.Walk root v) (hp : p.IsPath) :
    p = hG.rootPath root v :=
  (Classical.choose_spec (hG.existsUnique_path root v)).2 p hp

/-- The canonical tree path is a shortest path. -/
theorem IsTree.rootPath_length_eq_dist
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) :
    (hG.rootPath root v).length = G.dist root v := by
  obtain ⟨p, hp, hlen⟩ :=
    hG.connected.exists_path_of_dist root v
  have hpv : p = hG.rootPath root v :=
    hG.rootPath_unique root v p hp
  simpa [hpv] using hlen

/-- Parent with respect to a chosen root. At the root, this returns the root. -/
noncomputable def IsTree.parent
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) : V :=
  (hG.rootPath root v).penultimate

/-- A non-root vertex is adjacent to its parent. -/
theorem IsTree.parent_adj
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (hvr : v ≠ root) :
    G.Adj (hG.parent root v) v := by
  exact
    (hG.rootPath root v).adj_penultimate
      (SimpleGraph.Walk.not_nil_of_ne hvr.symm)

/-- The parent lies exactly one graph-distance closer to the root. -/
theorem IsTree.parent_dist_add_one
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (hvr : v ≠ root) :
    G.dist root (hG.parent root v) + 1 =
      G.dist root v := by
  let p := hG.rootPath root v
  have hp : p.IsPath := hG.rootPath_isPath root v
  have hnp : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hvr.symm
  have hdrop : p.dropLast.IsPath := hp.dropLast
  have huniq :
      p.dropLast =
        hG.rootPath root (hG.parent root v) := by
    exact
      hG.rootPath_unique
        root (hG.parent root v) p.dropLast hdrop
  have hparent :=
    hG.rootPath_length_eq_dist
      root (hG.parent root v)
  have hv := hG.rootPath_length_eq_dist root v
  calc
    G.dist root (hG.parent root v) + 1 =
        (hG.rootPath root (hG.parent root v)).length + 1 := by
          rw [hparent]
    _ = p.dropLast.length + 1 := by rw [← huniq]
    _ = p.length := p.length_dropLast_add_one hnp
    _ = G.dist root v := hv

/-- A neighbour of the endpoint that already lies on the root path is its
parent. -/
theorem IsTree.eq_parent_of_adj_of_mem_rootPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v w : V)
    (hvr : v ≠ root)
    (hadj : G.Adj v w)
    (hw : w ∈ (hG.rootPath root v).support) :
    w = hG.parent root v := by
  exact
    hG.isAcyclic.eq_penultimate_of_adj_end
      (hG.rootPath_isPath root v)
      hadj
      hw

/-- A neighbour of v not already on the root path is a child of v. -/
theorem IsTree.parent_eq_of_adj_of_not_mem_rootPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v w : V)
    (hwr : w ≠ root)
    (hadj : G.Adj v w)
    (hw : w ∉ (hG.rootPath root v).support) :
    hG.parent root w = v := by
  have hpath :
      (hG.rootPath root v).concat hadj =
        hG.rootPath root w := by
    apply hG.rootPath_unique
    exact
      (hG.rootPath_isPath root v).concat hw hadj
  change (hG.rootPath root w).penultimate = v
  rw [← hpath]
  simp

end SimpleGraph

end StructuralRamsey.Girth
