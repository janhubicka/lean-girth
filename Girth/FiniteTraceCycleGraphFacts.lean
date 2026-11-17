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

universe v

/-- Every cyclic successor pair is an edge in the usual k-cycle. -/
theorem standardCycle_adj_finRotate
    {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    (SimpleGraph.cycleGraph k).Adj i (finRotate k i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 :=
    ⟨k - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  right
  rw [finRotate_apply]
  simp

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
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
  have hRotateI : finRotate (n + 2) i = i + 1 := finRotate_apply i
  have hRotateJ : finRotate (n + 2) j = j + 1 := finRotate_apply j
  have hTwice : i + 1 + 1 = i := by
    rw [← hRotateI, ← h', ← hRotateJ, ← h]
  have hZero : (1 : Fin (n + 2)) + 1 = 0 :=
    add_left_cancel (show i + (1 + 1) = i + 0 from by simpa [add_assoc] using hTwice)
  have hValue := congrArg Fin.val hZero
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero] at hValue
  rw [Nat.mod_eq_of_lt (by omega)] at hValue
  omega

/-- The cycle graph of length at least four has no triangle. -/
theorem standardCycle_cliqueFree_three
    {k : ℕ} (hk : 4 ≤ k) :
    (SimpleGraph.cycleGraph k).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨i, j, l, hij, hil, hjl, _⟩ :=
    ((SimpleGraph.cycleGraph k).is3Clique_iff).mp hs
  have impossible (a b c : Fin k) (hAB : a.val ≤ b.val) (hBC : b.val ≤ c.val)
      (hABAdj : (SimpleGraph.cycleGraph k).Adj a b)
      (hBCAdj : (SimpleGraph.cycleGraph k).Adj b c)
      (hACAdj : (SimpleGraph.cycleGraph k).Adj a c) : False := by
    have h₁ := (cycleGraph_adj_iff_of_val_le hk a b hAB).mp hABAdj
    have h₂ := (cycleGraph_adj_iff_of_val_le hk b c hBC).mp hBCAdj
    have h₃ := (cycleGraph_adj_iff_of_val_le hk a c (hAB.trans hBC)).mp hACAdj
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    omega
  rcases le_total i.val j.val with hiLEj | hjLEi
  · rcases le_total j.val l.val with hjLEl | hlLEj
    · exact impossible i j l hiLEj hjLEl hij hjl hil
    · rcases le_total i.val l.val with hiLEl | hlLEi
      · exact impossible i l j hiLEl hlLEj hil hjl.symm hij
      · exact impossible l i j hlLEi hiLEj hil.symm hij hjl.symm
  · rcases le_total i.val l.val with hiLEl | hlLEi
    · exact impossible j i l hjLEi hiLEl hij.symm hil hjl
    · rcases le_total j.val l.val with hjLEl | hlLEj
      · exact impossible j l i hjLEl hlLEi hjl hil.symm hij.symm
      · exact impossible l j i hlLEj hjLEi hjl.symm hij.symm hil.symm

/-- No induced cycle of length between four and q can occur in
the trace graph of an internally q-tree-completable ORIGINAL
cover. All finite-cycle arithmetic inputs are now supplied by
the preceding three source lemmas, not additional assumptions. -/
theorem no_bounded_induced_trace_cycle
    {W ι : Type v} [Fintype ι]
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
