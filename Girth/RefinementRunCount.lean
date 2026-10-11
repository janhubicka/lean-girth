import Mathlib.Tactic

/-!
# Finite run arithmetic in the singleton-part refinement girth gain

In the manuscript's first-wagon refinement argument a hypothetical
Berge cycle projects to a cycle of distinct child wagons. At the
least common ancestor with a singleton allowed intersection part,
the two boundary connectors of every nonempty child run lie in that
same part. A single transversal edge cannot join two such distinct
vertices, so every run has at least two edges.

The projected child-cycle girth hypothesis then supplies at least
g+1 runs, and the total length of the original cycle is at least
2(g+1). This module checks the FINITE ARITHMETIC, independently of
how the child runs and their connectors are extracted from an actual
train and its nested equivalences.

The geometric run decomposition is NOT proved by these arithmetic
lemmas, and the manuscript's complete train increment remains open.
-/

namespace StructuralRamsey.Girth

/-- A finite list of run lengths, each at least two, contains at
least twice its number of runs in total edge occurrences. -/
theorem refinementRun_sum_ge_two_length
    (runs : List ℕ)
    (hAtLeastTwo : ∀ n ∈ runs, 2 ≤ n) :
    2 * runs.length ≤ runs.sum := by
  induction runs with
  | nil => simp
  | cons n ns ih =>
      have hn : 2 ≤ n := hAtLeastTwo n (by simp)
      have hrest : ∀ k ∈ ns, 2 ≤ k := by
        intro k hk
        exact hAtLeastTwo k (by simp [hk])
      have hbound := ih hrest
      simp only [List.length_cons, List.sum_cons]
      omega

/-- If the quotient child walk has at least g+1 runs, then the
uncompressed cycle has length at least 2g+2. -/
theorem refinementRun_length_ge_two_g_plus_two
    (g : ℕ) (runs : List ℕ)
    (hAtLeastTwo : ∀ n ∈ runs, 2 ≤ n)
    (hManyRuns : g + 1 ≤ runs.length) :
    2 * (g + 1) ≤ runs.sum := by
  have h := refinementRun_sum_ge_two_length runs hAtLeastTwo
  omega

/-- This is strictly more than the original required cutoff g+1,
so refinement through one permitted part gains a unit of girth. -/
theorem refinementRun_length_gt_g_plus_one
    (g : ℕ) (runs : List ℕ)
    (hAtLeastTwo : ∀ n ∈ runs, 2 ≤ n)
    (hManyRuns : g + 1 ≤ runs.length) :
    g + 1 < runs.sum := by
  have h := refinementRun_length_ge_two_g_plus_two
    g runs hAtLeastTwo hManyRuns
  omega

end StructuralRamsey.Girth
