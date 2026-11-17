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

end StructuralRamsey.Girth
