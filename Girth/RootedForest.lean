import Girth.Forest
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # Rooting join trees

This module isolates the ordinary graph-theoretic skeleton of Remark 4.2.
A rooted tree has a canonical unique root-to-node path; the parent of a
non-root node is its penultimate vertex and lies exactly one level closer to
the root.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

namespace JoinTree

/-- The unique path from the chosen root to a member of a join tree. -/
noncomputable def rootPath {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) :
    J.tree.Walk root i :=
  Classical.choose (J.isTree.existsUnique_path root i)

theorem rootPath_isPath {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) :
    (J.rootPath root i).IsPath :=
  (Classical.choose_spec (J.isTree.existsUnique_path root i)).1

theorem rootPath_unique {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι)
    (p : J.tree.Walk root i) (hp : p.IsPath) :
    p = J.rootPath root i :=
  (Classical.choose_spec (J.isTree.existsUnique_path root i)).2 p hp

/-- In a tree the canonical path is a shortest path. -/
theorem rootPath_length_eq_dist {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) :
    (J.rootPath root i).length = J.tree.dist root i := by
  obtain ⟨p, hp, hlen⟩ :=
    J.isTree.connected.exists_path_of_dist root i
  have hpi : p = J.rootPath root i :=
    J.rootPath_unique root i p hp
  simpa [hpi] using hlen

/-- Parent in the rooted join tree.  At the root this definition returns the
root itself because `Walk.penultimate` does so for a nil walk. -/
noncomputable def parent {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) : ι :=
  (J.rootPath root i).penultimate

/-- A non-root member is adjacent to its parent. -/
theorem parent_adj {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) (hri : i ≠ root) :
    J.tree.Adj (J.parent root i) i := by
  exact (J.rootPath root i).adj_penultimate
    (SimpleGraph.Walk.not_nil_of_ne hri.symm)

/-- The parent is exactly one level closer to the root. -/
theorem parent_dist_add_one {F : ι → HypergraphPiece W}
    (J : JoinTree F) (root i : ι) (hri : i ≠ root) :
    J.tree.dist root (J.parent root i) + 1 =
      J.tree.dist root i := by
  let p := J.rootPath root i
  have hp : p.IsPath := J.rootPath_isPath root i
  have hnp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hri.symm
  have hdrop : p.dropLast.IsPath := hp.dropLast
  have huniq :
      p.dropLast = J.rootPath root (J.parent root i) := by
    exact J.rootPath_unique root (J.parent root i) p.dropLast hdrop
  have hparent :=
    J.rootPath_length_eq_dist root (J.parent root i)
  have hi := J.rootPath_length_eq_dist root i
  calc
    J.tree.dist root (J.parent root i) + 1 =
        (J.rootPath root (J.parent root i)).length + 1 := by
          rw [hparent]
    _ = p.dropLast.length + 1 := by rw [← huniq]
    _ = p.length := p.length_dropLast_add_one hnp
    _ = J.tree.dist root i := by
      exact hi

end JoinTree

end StructuralRamsey.Girth
