import Girth.FiniteTraceChordlessPattern

/-!
# Deriving the cross-pair certificate from triangle exclusion

The direct cyclic-pair obstruction asks for a nonadjacent pair
among the endpoints of each two different required edges.
An induced cycle of length at least four is triangle-free, so
there is a more economical interface: the second required edge
has an endpoint outside the first edge, and this endpoint cannot
be adjacent to both ends of the first edge.

This source lemma reduces the potentially awkward cycle-index
arithmetic to two standard elementary facts:
1. the edges of the cycle are pairwise distinct as 2-sets;
2. its induced graph is triangle-free.

It does not assert either fact for arbitrary graphs and does
not replace a missing proof with an axiom.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- An endpoint of the second edge lying outside the first must
miss at least one endpoint of the first when no triangle is
allowed on the required-pair vertices. -/
theorem crossPairNonedge_of_noTriangle
    (G : SimpleGraph W) (a b : E → W)
    (e f : E) (hef : e ≠ f)
    (hThird :
      ∃ z : W,
        (z = a f ∨ z = b f) ∧ z ≠ a e ∧ z ≠ b e)
    (hNoTriangle :
      ∀ z : W,
        (z = a f ∨ z = b f) →
        z ≠ a e → z ≠ b e →
          ¬ (G.Adj (a e) z ∧ G.Adj (b e) z)) :
    CrossPairNonedge G a b e f := by
  obtain ⟨z, hzEnd, hza, hzb⟩ := hThird
  have hzListed :
      z = a e ∨ z = b e ∨ z = a f ∨ z = b f := by
    rcases hzEnd with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  by_cases haz : G.Adj (a e) z
  · have hbz : ¬ G.Adj (b e) z := by
      intro hbz
      exact hNoTriangle z hzEnd hza hzb ⟨haz, hbz⟩
    exact ⟨b e, z, hzb.symm,
      Or.inr (Or.inl rfl), hzListed, hbz⟩
  · exact ⟨a e, z, hza.symm,
      Or.inl rfl, hzListed, haz⟩

/-- The generic bounded chordless-pair obstruction follows from
the simpler endpoint-distinctness and triangle-exclusion data.
These are the properties supplied by an induced simple cycle
of length at least four. -/
theorem no_bounded_trianglefree_pair_pattern
    [Fintype W] [Fintype E] [Nonempty E]
    (G : SimpleGraph W) (a b : E → W)
    (hThird :
      ∀ e f : E, e ≠ f →
        ∃ z : W,
          (z = a f ∨ z = b f) ∧ z ≠ a e ∧ z ≠ b e)
    (hNoTriangle :
      ∀ e f : E, e ≠ f →
        ∀ z : W,
          (z = a f ∨ z = b f) →
          z ≠ a e → z ≠ b e →
            ¬ (G.Adj (a e) z ∧ G.Adj (b e) z)) :
    ∀ e f : E, e ≠ f →
      CrossPairNonedge G a b e f := by
  intro e f hef
  exact crossPairNonedge_of_noTriangle
    G a b e f hef (hThird e f hef)
    (hNoTriangle e f hef)

end StructuralRamsey.Girth
