import Girth.ForestFiniteSetCompletion

/-!
# Finite sets of selected copies versus support-piece completions

The structural manuscript quantifies over finite sets of actual A/B copies.
The generic Lean completion predicate quantifies over finite families of
their *complete support pieces*. These are not literally the same type:
two copies may have equal supports, and the support map need not be injective.

This adapter makes no faithfulness or injectivity assumption. To complete
an indexed family of tested support pieces, choose a legitimate source
label for each, take the finite SET of selected source labels, apply the
copy-set completion property, and transfer the resulting support forest.
The number of distinct labels is bounded by the original selection size.

All completed auxiliary members still have to be genuine designated
support pieces. No arbitrary-subfamily heredity is used.

Candidate source only; Lean elaboration and #print axioms are pending.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Label : Type v}

/-- Finite-SET forest extension for labels of actual copies, where
the join-tree forest is formed by their complete support pieces.
The support map need not be injective. -/
def FinsetLabelForestCompletionProperty
    (support : Label → HypergraphPiece W)
    (eligible : Label → Prop)
    (designated : HypergraphPiece W → Prop)
    (m : ℕ) : Prop :=
  ∀ s : Finset Label,
    (∀ a : Label, a ∈ s → eligible a) →
    s.card ≤ m →
      ∃ (K : Type v), ∃ (finite : Fintype K),
        letI : Fintype K := finite
        ∃ completed : K → HypergraphPiece W,
          ForestOfCopies completed ∧
          (∀ a : Label, a ∈ s →
            ∃ k : K, completed k = support a) ∧
          (∀ k : K,
            (∃ a : Label, a ∈ s ∧
              completed k = support a) ∨ designated (completed k))

/-- Every tested support piece has at least one legitimate copy label,
and the finite-set extension property for such labels implies the
indexed support-piece forest-completion property. This handles
repeated support pieces and repeated labels without assuming
an injective support map. -/
theorem FinsetLabelForestCompletionProperty.toSupportIndexed
    {support : Label → HypergraphPiece W}
    {eligible : Label → Prop}
    {designated tested : HypergraphPiece W → Prop}
    {m : ℕ}
    (hSet : FinsetLabelForestCompletionProperty
      support eligible designated m)
    (hRepresentation : ∀ P : HypergraphPiece W, tested P →
      ∃ a : Label, eligible a ∧ support a = P) :
    ForestCompletionProperty tested designated m := by
  classical
  intro N hFinite selected hTest hCard
  letI : Fintype N := hFinite
  have hPreimage (n : N) :
      ∃ a : Label, eligible a ∧ support a = selected n :=
    hRepresentation (selected n) (hTest n)
  choose picked hPickedEligible hPickedSupport using hPreimage
  let s : Finset Label := Finset.univ.image picked
  have hEligible :
      ∀ a : Label, a ∈ s → eligible a := by
    intro a ha
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp ha
    rw [← hn]
    exact hPickedEligible n
  have hBudget : s.card ≤ m := by
    have hImage : s.card ≤ Fintype.card N := by
      simpa only [s, Finset.card_univ] using
        (Finset.card_image_le
          (s := (Finset.univ : Finset N)) (f := picked))
    exact hImage.trans hCard
  obtain ⟨K, finite, completed, hForest, hContains, hOnly⟩ :=
    hSet s hEligible hBudget
  letI : Fintype K := finite
  refine ⟨K, finite, completed, hForest, ?_, ?_⟩
  · intro n
    obtain ⟨k, hk⟩ := hContains (picked n)
      (Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩)
    exact ⟨k, hk.trans (hPickedSupport n)⟩
  · intro k
    rcases hOnly k with ⟨a, ha, hk⟩ | hDesignated
    · obtain ⟨n, _, hn⟩ := Finset.mem_image.mp ha
      left
      refine ⟨n, ?_⟩
      calc
        completed k = support a := hk
        _ = support (picked n) := congrArg support hn.symm
        _ = selected n := hPickedSupport n
    · exact Or.inr hDesignated

/-- Conversely, completing finite SETS of support pieces already
completes finite sets of original copy labels, with no injectivity
assumption on the support map. Image cardinality never increases.
This isolates the precise step between the two set-based
formulations of the manuscript's forest-extension property. -/
theorem FinsetForestCompletionProperty.toLabelFinset
    {tested designated : HypergraphPiece W → Prop}
    {m : ℕ}
    (hSet : FinsetForestCompletionProperty tested designated m)
    (support : Label → HypergraphPiece W)
    (eligible : Label → Prop)
    (hTest : ∀ a : Label, eligible a → tested (support a)) :
    FinsetLabelForestCompletionProperty support eligible designated m := by
  classical
  intro selected hEligible hCard
  let supportSet : Finset (HypergraphPiece W) :=
    selected.image support
  have hSupportTest :
      ∀ P : HypergraphPiece W, P ∈ supportSet → tested P := by
    intro P hP
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hP
    rw [← hEq]
    exact hTest a (hEligible a ha)
  have hSupportCard : supportSet.card ≤ m := by
    have hImage :
        supportSet.card ≤ selected.card := by
      simpa only [supportSet] using
        (Finset.card_image_le (s := selected) (f := support))
    exact hImage.trans hCard
  obtain ⟨K, finite, completed, hForest, hContains, hOnly⟩ :=
    hSet supportSet hSupportTest hSupportCard
  letI : Fintype K := finite
  refine ⟨K, finite, completed, hForest, ?_, ?_⟩
  · intro a ha
    exact hContains (support a)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · intro k
    rcases hOnly k with hSelected | hDesignated
    · left
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hSelected
      exact ⟨a, ha, hEq.symm⟩
    · exact Or.inr hDesignated

end StructuralRamsey.Girth
