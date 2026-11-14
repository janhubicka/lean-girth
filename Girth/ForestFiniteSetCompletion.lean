import Girth.ForestCompletionProperty

/-!
# From finite sets of support pieces to indexed forest completions

The manuscript quantifies over finite *sets* of actual selected
support pieces. The existing Lean invariant
`ForestCompletionProperty` quantifies over finite *indexed
families*, which may repeat the same underlying piece.

To use a finite-set hypothesis without silently assuming an
injective selection, first take the image of the indexed family.
Its cardinality does not exceed the original index cardinality.
A completion of that image then covers every selected index, and
each surviving member is selected or permitted designated.

This is an interface adapter, not a Ramsey-witness theorem.
It does not by itself identify relational copies with support pieces
or certify the revised manuscript until the statements are matched.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- The unlabelled finite-set formulation of bounded forest
completion, with the same allowed additional designated pieces. -/
def FinsetForestCompletionProperty
    (tested designated : HypergraphPiece W → Prop)
    (m : ℕ) : Prop :=
  ∀ s : Finset (HypergraphPiece W),
    (∀ T : HypergraphPiece W, T ∈ s → tested T) →
    s.card ≤ m →
      ∃ (K : Type v), ∃ (finite : Fintype K),
        letI : Fintype K := finite
        ∃ completed : K → HypergraphPiece W,
          ForestOfCopies completed ∧
          (∀ T : HypergraphPiece W, T ∈ s →
            ∃ k : K, completed k = T) ∧
          (∀ k : K, completed k ∈ s ∨ designated (completed k))

/-- A completion property for sets of distinct support pieces also
handles labelled families with duplicate members. The only
cardinality step is card(image(selected)) ≤ card(selected indices).
No arbitrary-subfamily heredity of forests is invoked. -/
theorem FinsetForestCompletionProperty.toIndexed
    {tested designated : HypergraphPiece W → Prop}
    {m : ℕ}
    (h : FinsetForestCompletionProperty tested designated m) :
    ForestCompletionProperty tested designated m := by
  classical
  intro N hFinite selected hTest hCard
  letI : Fintype N := hFinite
  let s : Finset (HypergraphPiece W) := Finset.univ.image selected
  have hTestS :
      ∀ T : HypergraphPiece W, T ∈ s → tested T := by
    intro T hT
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hT
    rw [← hn]
    exact hTest n
  have hBoundS : s.card ≤ m := by
    have hImage :
        s.card ≤ Fintype.card N := by
      simpa only [s, Finset.card_univ] using
        (Finset.card_image_le
          (s := (Finset.univ : Finset N)) (f := selected))
    exact hImage.trans hCard
  obtain ⟨K, finite, completed, hForest, hContains, hOnly⟩ :=
    h s hTestS hBoundS
  letI : Fintype K := finite
  refine ⟨K, finite, completed, hForest, ?_, ?_⟩
  · intro n
    apply hContains
    exact Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩
  · intro k
    rcases hOnly k with hSelected | hDesignated
    · left
      obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hSelected
      exact ⟨n, hn.symm⟩
    · exact Or.inr hDesignated

end StructuralRamsey.Girth
