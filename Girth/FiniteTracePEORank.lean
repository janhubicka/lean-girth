import Girth.FiniteTraceSimplicialCriterion
import Mathlib.Order.Basic

/-!
# Turn a finite elimination ranking into an actual LinearOrder

This is the order-construction adapter for the standard Dirac
simplicial-vertex proof of chordal graphs.  It does NOT assume a
perfect elimination order: it takes an explicit injective ranking
whose strictly later neighbours have the clique property.

Mathlib's LinearOrder.lift' creates the genuine order from that
ranking. The remaining hard theorem constructs the ranking by
repeatedly choosing a simplicial vertex in induced subgraphs.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- A numerical certificate for a perfect elimination ordering. -/
def IsPerfectEliminationRanking
    (G : SimpleGraph V) (rank : V → ℕ) : Prop :=
  Function.Injective rank ∧
    ∀ v x y : V,
      rank v < rank x → rank v < rank y → x ≠ y →
        G.Adj v x → G.Adj v y → G.Adj x y

/-- A valid injective ranking canonically induces a linear order
for which the graph has the PEO property. No cycle theorem is
being postulated by this adapter. -/
theorem exists_perfectEliminationOrder_of_ranking
    (G : SimpleGraph V) (rank : V → ℕ)
    (hRank : IsPerfectEliminationRanking G rank) :
    ∃ order : LinearOrder V,
      @IsPerfectEliminationOrder V order G := by
  let order : LinearOrder V :=
    LinearOrder.lift' rank hRank.1
  refine ⟨order, ?_⟩
  change ∀ v x y : V,
    rank v < rank x → rank v < rank y → x ≠ y →
      G.Adj v x → G.Adj v y → G.Adj x y
  exact hRank.2

end StructuralRamsey.Girth
