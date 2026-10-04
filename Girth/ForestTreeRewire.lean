import Girth.FiberConnectedTree
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Rewiring a deleted vertex of a join tree

The one-edge deletion argument replaces the star at the deleted join-tree node
by a tree on its former neighbours.  This file collects the finite graph
lemmas needed for that surgery.
-/

namespace StructuralRamsey.Girth

universe v

/-- A finite connected graph with exactly one fewer edge than vertices is a
tree.  We use this after replacing the deleted star by a tree on its
neighbours. -/
theorem isTree_of_connected_card_edgeFinset
    {V : Type v} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcard : #G.edgeFinset + 1 = Fintype.card V) :
    G.IsTree := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hconn.exists_isTree_le
  have hTcard : #T.edgeFinset + 1 = Fintype.card V :=
    hTtree.card_edgeFinset
  have hcards : #T.edgeFinset = #G.edgeFinset := by
    omega
  have hsub : T.edgeFinset ⊆ G.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hTG
  have hedge : T.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hEq : T = G :=
    SimpleGraph.edgeFinset_inj.1 hedge
  simpa [hEq] using hTtree

end StructuralRamsey.Girth
