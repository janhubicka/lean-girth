import Girth.FiniteTraceEliminationBags

/-!
# Simplicial vertices and perfect elimination orders

Definitions and elementary consequences used to isolate the standard
Dirac theorem still missing from the primary small-trace validation.
No chordal -> PEO theorem is claimed here.

A vertex is simplicial within an induced vertex set if all its
neighbours in that set form a clique. A perfect elimination order
is precisely an order in which every vertex is simplicial among
the vertices not earlier than it.

The hard missing step is proving that every nonempty induced
subgraph of a finite chordal graph has a simplicial vertex
(Dirac's theorem). That step must be proved separately, not
added as an axiom.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The neighbours of v lying in S form a clique. -/
def IsSimplicialWithin
    (G : SimpleGraph V) (S : Set V) (v : V) : Prop :=
  ∀ x : V, x ∈ S →
    ∀ y : V, y ∈ S → x ≠ y →
      G.Adj v x → G.Adj v y → G.Adj x y

/-- Simpliciality in a larger vertex set implies simpliciality
in every smaller one. -/
theorem IsSimplicialWithin.mono
    (G : SimpleGraph V) {S T : Set V} {v : V}
    (hST : S ⊆ T)
    (hS : IsSimplicialWithin G T v) :
    IsSimplicialWithin G S v := by
  intro x hx y hy hxy hvx hvy
  exact hS x (hST hx) y (hST hy) hxy hvx hvy

/-- The exact clique characterization, with no requirement that
v belongs to S. -/
theorem isSimplicialWithin_iff_clique
    (G : SimpleGraph V) (S : Set V) (v : V) :
    IsSimplicialWithin G S v ↔
      G.IsClique {x : V | x ∈ S ∧ G.Adj v x} := by
  constructor
  · intro h x hx y hy hxy
    exact h x hx.1 y hy.1 hxy hx.2 hy.2
  · intro h x hx y hy hxy hvx hvy
    exact h x ⟨hx, hvx⟩ y ⟨hy, hvy⟩ hxy

/-- The PEO condition is just simpliciality of each vertex
within its own suffix. -/
theorem isPerfectEliminationOrder_iff_simplicialSuffix
    [LinearOrder V] (G : SimpleGraph V) :
    IsPerfectEliminationOrder G ↔
      ∀ v : V, IsSimplicialWithin G {x : V | v ≤ x} v := by
  constructor
  · intro hPEO v x hx y hy hxy hvx hvy
    have hvxStrict : v < x := lt_of_le_of_ne hx (by
      intro h
      subst x
      exact hvx.ne rfl)
    have hvyStrict : v < y := lt_of_le_of_ne hy (by
      intro h
      subst y
      exact hvy.ne rfl)
    exact hPEO v x y hvxStrict hvyStrict hxy hvx hvy
  · intro hSuffix v x y hvx hvy hxy hvxAdj hvyAdj
    exact hSuffix v x (le_of_lt hvx) y (le_of_lt hvy)
      hxy hvxAdj hvyAdj

end StructuralRamsey.Girth
