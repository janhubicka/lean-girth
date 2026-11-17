import Girth.FiniteTraceCycleCertificate
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.GroupTheory.Perm.Fin

/-!
# The three arithmetic facts for the standard finite cycle graph

All three facts needed by the induced-cycle-to-forest obstruction
come from the pinned Mathlib definitions:
* consecutive vertices, indexed by finRotate k, are adjacent;
* the k unordered consecutive edge sets are pairwise different;
* for k >= 4, SimpleGraph.cycleGraph k has no triangle.

The only arithmetic needed is modular addition/subtraction in Fin k.
This file does NOT prove that every nonchordal graph possesses an
induced cycle, nor the finite chordal-to-PEO theorem.

IMPORTANT: source-level proof draft; not verified by Lean until
CheckTrack8Primary.lean is compiled and axioms printed.
-/

namespace StructuralRamsey.Girth

/-- Every cyclic successor pair is an edge in the usual k-cycle. -/
theorem standardCycle_adj_finRotate
    {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    (SimpleGraph.cycleGraph k).Adj i (finRotate k i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 :=
    ⟨k - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  right
  rw [finRotate_apply]
  fin_omega

/-- The unordered consecutive edges of a k-cycle are pairwise
distinct for k at least four.  In particular no two indices
encode the same undirected edge in opposite directions. -/
theorem standardCycle_distinct_finRotate_edges
    {k : ℕ} (hk : 4 ≤ k) :
    ∀ i j : Fin k, i ≠ j →
      ({i, finRotate k i} : Finset (Fin k)) ≠
        {j, finRotate k j} := by
  classical
  intro i j hij hp
  have hi : i = j ∨ i = finRotate k j := by
    have hmem : i ∈ ({j, finRotate k j} : Finset (Fin k)) := by
      rw [← hp]
      simp
    simpa using hmem
  have hj : j = i ∨ j = finRotate k i := by
    have hmem : j ∈ ({i, finRotate k i} : Finset (Fin k)) := by
      rw [hp]
      simp
    simpa using hmem
  rcases hi with h | h
  · exact hij h
  rcases hj with h' | h'
  · exact hij h'.symm
  have hRotI : finRotate k i = i + 1 := finRotate_apply i
  have hRotJ : finRotate k j = j + 1 := finRotate_apply j
  fin_omega

/-- The cycle graph of length at least four has no triangle. -/
theorem standardCycle_cliqueFree_three
    {k : ℕ} (hk : 4 ≤ k) :
    (SimpleGraph.cycleGraph k).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨i, j, l, hij, hil, hjl, _⟩ :=
    ((SimpleGraph.cycleGraph k).is3Clique_iff).mp hs
  have hij' := (SimpleGraph.cycleGraph_adj').mp hij
  have hil' := (SimpleGraph.cycleGraph_adj').mp hil
  have hjl' := (SimpleGraph.cycleGraph_adj').mp hjl
  fin_omega

/-- No induced cycle of length between four and q can occur in
the trace graph of an internally q-tree-completable ORIGINAL
cover. All finite-cycle arithmetic inputs are now supplied by
the preceding three source lemmas, not additional assumptions. -/
theorem no_bounded_induced_trace_cycle
    {W ι : Type*} [Fintype ι]
    (F : ι → Set W) (Z : Set W) (q k : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (hk : 4 ≤ k) (hBudget : k ≤ q)
    (v : Fin k → Z)
    (hInduced : IsInducedFinCycle (tracePairGraph F Z) k v) :
    False := by
  exact no_bounded_induced_fin_cycle_of_standard_cycle_facts
    F Z q k hLocal hk hBudget v hInduced
    (standardCycle_adj_finRotate hk)
    (standardCycle_distinct_finRotate_edges hk)
    (standardCycle_cliqueFree_three hk)

end StructuralRamsey.Girth
