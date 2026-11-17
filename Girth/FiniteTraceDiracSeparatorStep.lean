import Girth.FiniteTraceSimplicialCriterion

/-!
# Strong Dirac induction: the clique-separator gluing step

Suppose S is a clique separating two nonempty sides A,B in G.
If the smaller induced subgraphs on A union S and B union S
each satisfy Dirac's dichotomy (clique or two nonadjacent
simplicial vertices), then G has two nonadjacent simplicial
vertices, one on each side.

The only needed geometric information about the sides is:
1. each has a vertex outside S;
2. distinct sides have no common vertex and no connecting edge;
3. every ambient neighbour of a side vertex lies in its side
   union S (this is automatic for components of G minus S).

This proves the actual induction COMBINATION step from the
existing elementary simplicial lemmas. The remaining difficult
graph theory is only the minimal-separator-is-clique theorem and
an exact induction over induced finite subgraphs.

Source-level draft; do not claim kernel validation until built.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- The two-nonadjacent-simplicial-vertices alternative on a
specified induced vertex set. -/
def StrongDiracAlternative
    (G : SimpleGraph V) (T : Set V) : Prop :=
  G.IsClique T ∨
    ∃ u : V, u ∈ T ∧
      ∃ w : V, w ∈ T ∧ u ≠ w ∧
        ¬ G.Adj u w ∧
        IsSimplicialWithin G T u ∧
        IsSimplicialWithin G T w

/-- Two smaller sides of a clique separator supply two
nonadjacent simplicial vertices for the ambient graph. -/
theorem strongDirac_step_of_clique_separator
    (G : SimpleGraph V) (S A B : Set V)
    (hSClique : G.IsClique S)
    (hAOut : (A \ S).Nonempty)
    (hBOut : (B \ S).Nonempty)
    (hA : StrongDiracAlternative G (A ∪ S))
    (hB : StrongDiracAlternative G (B ∪ S))
    (hSeparate :
      ∀ u : V, u ∈ A →
        ∀ w : V, w ∈ B → u ≠ w ∧ ¬ G.Adj u w)
    (hANeighbours :
      ∀ u : V, u ∈ A →
        ∀ x : V, G.Adj u x → x ∈ A ∪ S)
    (hBNeighbours :
      ∀ w : V, w ∈ B →
        ∀ x : V, G.Adj w x → x ∈ B ∪ S) :
    ∃ u : V, u ∈ A ∧
      ∃ w : V, w ∈ B ∧ u ≠ w ∧
        ¬ G.Adj u w ∧
        IsSimplicialWithin G Set.univ u ∧
        IsSimplicialWithin G Set.univ w := by
  have hAOut' : ((A ∪ S) \ S).Nonempty := by
    obtain ⟨u, huA, huNotS⟩ := hAOut
    exact ⟨u, Or.inl huA, huNotS⟩
  have hBOut' : ((B ∪ S) \ S).Nonempty := by
    obtain ⟨w, hwB, hwNotS⟩ := hBOut
    exact ⟨w, Or.inl hwB, hwNotS⟩
  obtain ⟨u, hu, huSimp⟩ :=
    exists_simplicialOutside_clique
      G S (A ∪ S) hSClique hAOut' hA
  obtain ⟨w, hw, hwSimp⟩ :=
    exists_simplicialOutside_clique
      G S (B ∪ S) hSClique hBOut' hB
  have huA : u ∈ A := by
    rcases hu.1 with huA | huS
    · exact huA
    · exact (hu.2 huS).elim
  have hwB : w ∈ B := by
    rcases hw.1 with hwB | hwS
    · exact hwB
    · exact (hw.2 hwS).elim
  obtain ⟨huw, hNotAdj⟩ := hSeparate u huA w hwB
  have huAmbient : IsSimplicialWithin G Set.univ u :=
    isSimplicialWithin_univ_of_neighbors_subset
      G (A ∪ S) u (hANeighbours u huA) huSimp
  have hwAmbient : IsSimplicialWithin G Set.univ w :=
    isSimplicialWithin_univ_of_neighbors_subset
      G (B ∪ S) w (hBNeighbours w hwB) hwSimp
  exact ⟨u, huA, w, hwB, huw, hNotAdj,
    huAmbient, hwAmbient⟩

end StructuralRamsey.Girth
