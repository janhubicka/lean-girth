import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- An INDUCED cycle witness, unlike a bare graph embedding
of cycleGraph k.  The adjacency equivalence explicitly reflects
nonedges, ruling out false witnesses such as a 4-cycle in K4. -/
def IsInducedFinCycle
    {U : Type v} (G : SimpleGraph U) (k : ℕ)
    (v : Fin k → U) : Prop :=
  Function.Injective v ∧
    ∀ i j : Fin k,
      G.Adj (v i) (v j) ↔
        (SimpleGraph.cycleGraph k).Adj i j

/-- Absence of induced chordless cycles of length at least four.
A plain (not induced) graph cycle is intentionally insufficient. -/
def NoLongInducedCycles (G : SimpleGraph W) : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∀ v : Fin k → W, ¬ IsInducedFinCycle G k v

/-- Adjacency in a finite cycle written on ordered numerical indices. -/
theorem cycleGraph_adj_iff_of_val_le {k : ℕ} (hk : 4 ≤ k)
    (i j : Fin k) (hij : i.val ≤ j.val) :
    (SimpleGraph.cycleGraph k).Adj i j ↔
      i.val + 1 = j.val ∨ i.val = 0 ∧ j.val + 1 = k := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i = j
  · subst j
    simp only [SimpleGraph.irrefl, false_iff]
    omega
  · have hlt : i < j := lt_of_le_of_ne hij h
    rw [SimpleGraph.cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hlt, Fin.sub_val_of_le hij]
    omega

end StructuralRamsey.Girth
