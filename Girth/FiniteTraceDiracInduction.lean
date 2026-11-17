import Girth.FiniteTraceDiracSeparatorStep
import Girth.FiniteTracePEORank

/-!
# Perfect elimination from clique separators

It suffices to find a clique separator in each noncomplete induced subgraph.
The two sides can be distinct components of the graph after the separator is
removed. They need not account for every vertex outside the separator.
-/

namespace StructuralRamsey.Girth

universe v
variable {V : Type v}

/-- Two components of a graph induced on T after removing a clique S. -/
structure InducedCliqueSeparation (G : SimpleGraph V) (T : Finset V) where
  separator : Finset V
  first : Finset V
  second : Finset V
  separator_subset : separator ⊆ T
  first_subset : first ⊆ T
  second_subset : second ⊆ T
  clique : G.IsClique (separator : Set V)
  first_outside : ∃ x ∈ first, x ∉ separator
  second_outside : ∃ x ∈ second, x ∉ separator
  separate : ∀ x ∈ first, ∀ y ∈ second, x ≠ y ∧ ¬ G.Adj x y
  first_neighbours : ∀ x ∈ first, ∀ y ∈ T, G.Adj x y → y ∈ first ∨ y ∈ separator
  second_neighbours : ∀ x ∈ second, ∀ y ∈ T, G.Adj x y → y ∈ second ∨ y ∈ separator

/-- The finite strong Dirac induction when every noncomplete induced graph
has two nonempty sides separated by a clique. -/
theorem strongDirac_of_inducedCliqueSeparations (G : SimpleGraph V)
    (hSplit : ∀ T : Finset V, ¬ G.IsClique (T : Set V) →
      Nonempty (InducedCliqueSeparation G T))
    (T : Finset V) : StrongDiracAlternative G (T : Set V) := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hClique : G.IsClique (T : Set V)
    · exact Or.inl hClique
    obtain ⟨split⟩ := hSplit T hClique
    obtain ⟨x, hx, hxS⟩ := split.first_outside
    obtain ⟨y, hy, hyS⟩ := split.second_outside
    have hFirst : split.first ∪ split.separator ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset
        split.first_subset split.separator_subset, ?_⟩
      intro hEq
      have hyT := split.second_subset hy
      rw [← hEq, Finset.mem_union] at hyT
      rcases hyT with hyFirst | hySep
      · exact (split.separate y hyFirst y hy).1 rfl
      · exact hyS hySep
    have hSecond : split.second ∪ split.separator ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset
        split.second_subset split.separator_subset, ?_⟩
      intro hEq
      have hxT := split.first_subset hx
      rw [← hEq, Finset.mem_union] at hxT
      rcases hxT with hxSecond | hxSep
      · exact (split.separate x hx x hxSecond).1 rfl
      · exact hxS hxSep
    obtain ⟨a, ha, haSimp⟩ := exists_simplicialOutside_clique G
      (split.separator : Set V) ((split.first ∪ split.separator : Finset V) : Set V)
      split.clique ⟨x, Finset.mem_union_left _ hx, hxS⟩ (ih _ hFirst)
    obtain ⟨b, hb, hbSimp⟩ := exists_simplicialOutside_clique G
      (split.separator : Set V) ((split.second ∪ split.separator : Finset V) : Set V)
      split.clique ⟨y, Finset.mem_union_left _ hy, hyS⟩ (ih _ hSecond)
    have haFirst : a ∈ split.first :=
      (Finset.mem_union.mp ha.1).resolve_right ha.2
    have hbSecond : b ∈ split.second :=
      (Finset.mem_union.mp hb.1).resolve_right hb.2
    obtain ⟨hab, hNotAdj⟩ := split.separate a haFirst b hbSecond
    refine Or.inr ⟨a, split.first_subset haFirst, b, split.second_subset hbSecond,
      hab, hNotAdj, ?_, ?_⟩
    · intro u hu w hw huw hau haw
      exact haSimp u (Finset.mem_union.mpr (split.first_neighbours a haFirst u hu hau))
        w (Finset.mem_union.mpr (split.first_neighbours a haFirst w hw haw)) huw hau haw
    · intro u hu w hw huw hbu hbw
      exact hbSimp u (Finset.mem_union.mpr (split.second_neighbours b hbSecond u hu hbu))
        w (Finset.mem_union.mpr (split.second_neighbours b hbSecond w hw hbw)) huw hbu hbw

/-- Finite graphs with the induced clique-separation property have a PEO. -/
theorem exists_perfectEliminationOrder_of_inducedCliqueSeparations
    [Fintype V] (G : SimpleGraph V)
    (hSplit : ∀ T : Finset V, ¬ G.IsClique (T : Set V) →
      Nonempty (InducedCliqueSeparation G T)) :
    ∃ order : LinearOrder V, @IsPerfectEliminationOrder V order G := by
  apply exists_perfectEliminationOrder_of_simplicial_subsets G
  intro T hT
  rcases strongDirac_of_inducedCliqueSeparations G hSplit T with hClique | hTwo
  · obtain ⟨v, hv⟩ := hT
    exact ⟨v, hv, isSimplicialWithin_of_clique G (T : Set V) v hClique⟩
  · obtain ⟨v, hv, _, _, _, _, hvSimp, _⟩ := hTwo
    exact ⟨v, hv, hvSimp⟩

end StructuralRamsey.Girth
