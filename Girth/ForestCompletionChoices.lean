import Girth.ForestCompletionProperty

/-! # Choosing finite completion witnesses at the outer join-tree vertices

The circulation induction invokes the old forest-completion property
independently at finitely many standard-copy owners.  Each owner has a
possibly different finite family of selected members and connector pieces.
The quantified old invariant produces finite completed families uniformly;
the choice is made once, without enlarging the cardinal bound.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Choose a finite completed family at every owner from the old quantified
completion property.  The local index types may vary from owner to owner. -/
theorem ForestCompletionProperty.choose_local_completions
    {tested designated : HypergraphPiece W → Prop}
    {m : ℕ}
    (hOld : ForestCompletionProperty tested designated m)
    (N : Q → Type v)
    [∀ q, Fintype (N q)]
    (selected : (q : Q) → N q → HypergraphPiece W)
    (hTest : ∀ q (n : N q), tested (selected q n))
    (hBound : ∀ q, Fintype.card (N q) ≤ m) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
      ∃ (family : (q : Q) → K q → HypergraphPiece W),
        ∀ q,
          letI : Fintype (K q) := finite q
          ForestCompletionWitness (selected q) designated (family q) := by
  classical
  have hEach (q : Q) :
      ∃ (K : Type v), ∃ (finite : Fintype K),
        letI : Fintype K := finite
        ∃ family : K → HypergraphPiece W,
          ForestCompletionWitness (selected q) designated family := by
    exact hOld (N q) (selected q) (hTest q) (hBound q)
  choose K finite family hFamily using hEach
  exact ⟨K, finite, family, hFamily⟩

end StructuralRamsey.Girth
