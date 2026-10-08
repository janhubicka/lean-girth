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

/-- The exact local cardinal budget in the circulation induction.  At an
outer-tree owner q the request family consists of the selected members
assigned to q plus one connector request per adjacent owner.  Surjectivity
of the owner map pays for all connector requests out of the global budget. -/
theorem ForestCompletionProperty.choose_neighbor_local_completions
    {N : Type v}
    [Fintype N] [Fintype Q] [DecidableEq Q]
    {tested designated : HypergraphPiece W → Prop}
    {m : ℕ}
    (hOld : ForestCompletionProperty tested designated m)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (G : SimpleGraph Q)
    [DecidableRel G.Adj]
    (selected :
      (q : Q) →
        ({n : N // owner n = q} ⊕ G.neighborSet q) →
          HypergraphPiece W)
    (hTest :
      ∀ q (n : {n : N // owner n = q} ⊕ G.neighborSet q),
        tested (selected q n))
    (hCard : Fintype.card N ≤ m) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
      ∃ (family : (q : Q) → K q → HypergraphPiece W),
        ∀ q,
          letI : Fintype (K q) := finite q
          ForestCompletionWitness (selected q) designated (family q) := by
  classical
  have hBound (q : Q) :
      Fintype.card
        ({n : N // owner n = q} ⊕ G.neighborSet q) ≤ m := by
    rw [Fintype.card_sum, G.card_neighborSet_eq_degree q]
    exact (ownerFiber_card_add_degree_le owner hSurj G q).trans hCard
  exact ForestCompletionProperty.choose_local_completions
    hOld
    (fun q : Q =>
      {n : N // owner n = q} ⊕ G.neighborSet q)
    selected hTest hBound

/-- The owner-dependent form used in the circulation picture step: every
standard picture has its own transported tested and designated predicates.
The same global cardinal budget still supplies a finite completion at each
outer join-tree owner. -/
theorem ForestCompletionProperty.choose_neighbor_local_completions_dependent
    {N : Type v}
    [Fintype N] [Fintype Q] [DecidableEq Q]
    (tested designated : Q → HypergraphPiece W → Prop)
    {m : ℕ}
    (hOld :
      ∀ q : Q,
        ForestCompletionProperty (tested q) (designated q) m)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (G : SimpleGraph Q)
    [DecidableRel G.Adj]
    (selected :
      (q : Q) →
        ({n : N // owner n = q} ⊕ G.neighborSet q) →
          HypergraphPiece W)
    (hTest :
      ∀ q (n : {n : N // owner n = q} ⊕ G.neighborSet q),
        tested q (selected q n))
    (hCard : Fintype.card N ≤ m) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
      ∃ (family : (q : Q) → K q → HypergraphPiece W),
        ∀ q,
          letI : Fintype (K q) := finite q
          ForestCompletionWitness (selected q) (designated q)
            (family q) := by
  classical
  have hBound (q : Q) :
      Fintype.card
        ({n : N // owner n = q} ⊕ G.neighborSet q) ≤ m := by
    rw [Fintype.card_sum, G.card_neighborSet_eq_degree q]
    exact (ownerFiber_card_add_degree_le owner hSurj G q).trans hCard
  have hEach (q : Q) :
      ∃ (K : Type v), ∃ (finite : Fintype K),
        letI : Fintype K := finite
        ∃ family : K → HypergraphPiece W,
          ForestCompletionWitness
            (selected q) (designated q) family := by
    exact (hOld q)
      ({n : N // owner n = q} ⊕ G.neighborSet q)
      (selected q) (hTest q) (hBound q)
  choose K finite family hFamily using hEach
  exact ⟨K, finite, family, hFamily⟩

/-- Extract actual labels witnessing the inclusion of every local request
in its completed family.  This is what the outer join-tree assembly needs
to identify the selected pieces and to name one local separator connector
at each oriented tree edge. -/
theorem ForestCompletionProperty.choose_neighbor_local_completions_with_labels
    {N : Type v}
    [Fintype N] [Fintype Q] [DecidableEq Q]
    (tested designated : Q → HypergraphPiece W → Prop)
    {m : ℕ}
    (hOld :
      ∀ q : Q,
        ForestCompletionProperty (tested q) (designated q) m)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (G : SimpleGraph Q)
    [DecidableRel G.Adj]
    (selected :
      (q : Q) →
        ({n : N // owner n = q} ⊕ G.neighborSet q) →
          HypergraphPiece W)
    (hTest :
      ∀ q (n : {n : N // owner n = q} ⊕ G.neighborSet q),
        tested q (selected q n))
    (hCard : Fintype.card N ≤ m) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
      ∃ (family : (q : Q) → K q → HypergraphPiece W),
      ∃ (label : (q : Q) →
        ({n : N // owner n = q} ⊕ G.neighborSet q) → K q),
        ∀ q,
          letI : Fintype (K q) := finite q
          ForestCompletionWitness
            (selected q) (designated q) (family q) ∧
          ∀ n, family q (label q n) = selected q n := by
  classical
  obtain ⟨K, finite, family, hFamily⟩ :=
    ForestCompletionProperty.choose_neighbor_local_completions_dependent
      tested designated hOld owner hSurj G selected hTest hCard
  letI : ∀ q : Q, Fintype (K q) := finite
  have hLabel (q : Q)
      (n : {n : N // owner n = q} ⊕ G.neighborSet q) :
      ∃ k : K q, family q k = selected q n :=
    (hFamily q).2.1 n
  choose label hLabelSpec using hLabel
  refine ⟨K, finite, family, label, ?_⟩
  intro q
  exact ⟨hFamily q, hLabelSpec q⟩

end StructuralRamsey.Girth
