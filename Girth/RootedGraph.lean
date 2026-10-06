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
    (IsTree.rootPath hG root v).IsPath :=
  (Classical.choose_spec (hG.existsUnique_path root v)).1

theorem IsTree.rootPath_unique
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (p : G.Walk root v) (hp : p.IsPath) :
    p = IsTree.rootPath hG root v :=
  (Classical.choose_spec (hG.existsUnique_path root v)).2 p hp

/-- The canonical tree path is a shortest path. -/
theorem IsTree.rootPath_length_eq_dist
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) :
    (IsTree.rootPath hG root v).length = G.dist root v := by
  obtain ⟨p, hp, hlen⟩ :=
    hG.connected.exists_path_of_dist root v
  have hpv : p = IsTree.rootPath hG root v :=
    IsTree.rootPath_unique hG root v p hp
  simpa [hpv] using hlen

/-- Parent with respect to a chosen root. At the root, this returns the root. -/
noncomputable def IsTree.parent
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V) : V :=
  (IsTree.rootPath hG root v).penultimate

/-- A non-root vertex is adjacent to its parent. -/
theorem IsTree.parent_adj
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (hvr : v ≠ root) :
    G.Adj (IsTree.parent hG root v) v := by
  exact
    (IsTree.rootPath hG root v).adj_penultimate
      (SimpleGraph.Walk.not_nil_of_ne hvr.symm)

/-- The parent lies exactly one graph-distance closer to the root. -/
theorem IsTree.parent_dist_add_one
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v : V)
    (hvr : v ≠ root) :
    G.dist root (IsTree.parent hG root v) + 1 =
      G.dist root v := by
  let p := IsTree.rootPath hG root v
  have hp : p.IsPath := IsTree.rootPath_isPath hG root v
  have hnp : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hvr.symm
  have hdrop : p.dropLast.IsPath := hp.dropLast
  have huniq :
      p.dropLast =
        IsTree.rootPath hG root (IsTree.parent hG root v) := by
    exact
      IsTree.rootPath_unique hG
        root (IsTree.parent hG root v) p.dropLast hdrop
  have hparent :=
    IsTree.rootPath_length_eq_dist hG
      root (IsTree.parent hG root v)
  have hv := IsTree.rootPath_length_eq_dist hG root v
  calc
    G.dist root (IsTree.parent hG root v) + 1 =
        (IsTree.rootPath hG root (IsTree.parent hG root v)).length + 1 :=
      congrArg (fun n => n + 1) hparent.symm
    _ = p.dropLast.length + 1 :=
      congrArg (fun n => n + 1) (congrArg SimpleGraph.Walk.length huniq.symm)
    _ = p.length := p.length_dropLast_add_one hnp
    _ = G.dist root v := hv

/-- A neighbour of the endpoint that already lies on the root path is its
parent. -/
theorem IsTree.eq_parent_of_adj_of_mem_rootPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v w : V)
    (hvr : v ≠ root)
    (hadj : G.Adj v w)
    (hw : w ∈ (IsTree.rootPath hG root v).support) :
    w = IsTree.parent hG root v := by
  exact
    hG.isAcyclic.eq_penultimate_of_adj_end
      (IsTree.rootPath_isPath hG root v)
      hadj
      hw

/-- A neighbour of v not already on the root path is a child of v. -/
theorem IsTree.parent_eq_of_adj_of_not_mem_rootPath
    {G : SimpleGraph V}
    (hG : G.IsTree) (root v w : V)
    (hwr : w ≠ root)
    (hadj : G.Adj v w)
    (hw : w ∉ (IsTree.rootPath hG root v).support) :
    IsTree.parent hG root w = v := by
  have hpath :
      (IsTree.rootPath hG root v).concat hadj =
        IsTree.rootPath hG root w := by
    apply IsTree.rootPath_unique hG
    exact
      (IsTree.rootPath_isPath hG root v).concat hw hadj
  change (IsTree.rootPath hG root w).penultimate = v
  rw [← hpath]
  simp

end SimpleGraph

end StructuralRamsey.Girth
