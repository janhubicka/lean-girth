import Girth.LabelledWagonCutRestriction
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Why local child-girth does not imply girth of the first retained wagon cut

Consider the four physical edges of a path on five vertices:
  e0 = {0,1}, e1 = {1,2}, e2 = {2,3}, e3 = {3,4}.
The physical support is a path, hence has no Berge cycles.

At a coarser train cut group the two END edges e0 and e3 under
one labelled wagon A, leaving e1 and e2 as separate wagons B,C.
Their complete (unpruned) physical carriers then satisfy
  A ∩ B = {1}, B ∩ C = {2}, C ∩ A = {3}.
Consequently the THREE DISTINCT wagon labels have an actual
labelled Berge triangle, despite the original physical path being
acyclic. The two children e0,e3 of wagon A are disjoint, and every
other parent has only one child: all parent-local child girth
conditions hold.

This guards an invalid shortcut in the q>2 recursion: the existing
FirstWagonRefinement.childGirth supplies only girth WITHIN each
fixed parent. Even together with ordinary physical support girth,
it does not establish GLOBAL labelled girth of the first retained
parent cut. The #843 parent-to-children theorem correctly requires
that global parent-girth premise separately.

This is a combinatorial regression about arbitrary labelled trains,
not a counterexample to the forest-partite theorem. No appendix.
-/

namespace StructuralRamsey.Girth

/-- Four physical edges forming a path. -/
def fourEdgePath (e : Fin 4) : Set (Fin 5) :=
  {x | x.val = e.val ∨ x.val = e.val + 1}

/-- The end edges share a wagon label; the middle edges each have
a different label. -/
def fourEdgePathGroup (e : Fin 4) : Fin 3 :=
  if e.val = 0 ∨ e.val = 3 then 0
  else if e.val = 1 then 1 else 2

/-- The complete carrier of each physical wagon, without deleting
or identifying any of the four physical edges. -/
def groupedFourEdgePath (w : Fin 3) : Set (Fin 5) :=
  {x | ∃ e : Fin 4,
    fourEdgePathGroup e = w ∧ x ∈ fourEdgePath e}

/-- In the first parent wagon, its two original physical edges are
disjoint. Hence its child family creates no local cycle. -/
theorem fourEdgePath_end_edges_disjoint :
    Disjoint (fourEdgePath 0) (fourEdgePath 3) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change x.val = 0 ∨ x.val = 1 at hx
  change x.val = 3 ∨ x.val = 4 at hy
  omega

/-- The three distinct, grouped wagon labels form a real labelled
Berge triangle, with connectors 1,2,3. -/
def groupedFourEdgePath_triangle :
    LabelledBergeCycle groupedFourEdgePath where
  length := 3
  hlength := by decide
  label := id
  vertex := fun i => ⟨i.val + 1, by omega⟩
  label_injective := by
    intro i j h
    exact h
  vertex_injective := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp at hval
    omega
  left_mem := by
    intro i
    fin_cases i <;> decide
  right_mem := by
    intro i
    fin_cases i <;> decide

/-- The grouped wagon cut fails labelled girth greater than three,
even though its physical components form a path and the only
non-singleton parent has disjoint children. -/
theorem groupedFourEdgePath_not_labelledGirthGT_three :
    ¬ LabelledGirthGT groupedFourEdgePath 3 := by
  intro h
  exact h ⟨groupedFourEdgePath_triangle, by decide⟩

end StructuralRamsey.Girth
