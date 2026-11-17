import Girth.ForestTraceCyclicPairs
import Girth.ForestTraceLocalCompletion

/-!
# Bounded local completions exclude chordless pair patterns

The previous leaf-induction theorem forbids cyclic required pairs
in ANY join-tree family if one bag cannot contain two required pairs.
This module combines it with the actual internal local-completion
premise on ORIGINAL cover indices, without assuming a global join tree.

For an induced chordless cycle on k vertices, the required pairs
are its k consecutive edges. Adjacent edge endpoints belong to
some original bag, each endpoint lies on a second consecutive
edge, and a single original bag cannot contain two distinct
cycle edges without also containing a nonconsecutive pair.
Thus this exact theorem is the combinatorial core of the
"local completion implies chordality" step.

The adapter from SimpleGraph's concrete cyclic walks / Fin k to
these required-pair data is still open; no global chordality
theorem or maximal-clique join tree is asserted here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι E : Type v}

/-- Any required-pair cycle of at most q edges, whose different
edges can never be covered together by an original bag, prevents
bounded internal join-tree completion. This conclusion depends
only on the given ORIGINAL-index cover and its internal
completion property. -/
theorem no_cyclic_unique_pairs_of_internal_completion
    [Fintype ι] [Fintype E] [Nonempty E]
    (F : ι → Set W)
    (q : ℕ)
    (hLocal : HasInternalJoinTreeCompletions F q)
    (a b : E → W)
    (e₀ e₁ : E) (he : e₀ ≠ e₁)
    (hCard : Fintype.card E ≤ q)
    (hOtherA :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = a e ∨ b f = a e))
    (hOtherB :
      ∀ e : E, ∃ f : E, f ≠ e ∧
        (a f = b e ∨ b f = b e))
    (hPairs :
      ∀ e : E, ∃ i : ι,
        a e ∈ F i ∧ b e ∈ F i)
    (hUnique :
      ∀ i : ι, ∀ e f : E, e ≠ f →
        (a e ∈ F i ∧ b e ∈ F i) →
        (a f ∈ F i ∧ b f ∈ F i) → False) :
    False := by
  classical
  have hChosen (e : E) :
      ∃ i : ι, a e ∈ F i ∧ b e ∈ F i :=
    hPairs e
  let choose : E → ι :=
    fun e => Classical.choose (hChosen e)
  have hChoose (e : E) :
      a e ∈ F (choose e) ∧ b e ∈ F (choose e) :=
    Classical.choose_spec (hChosen e)
  let N : Finset ι :=
    (Finset.univ : Finset E).image choose
  have hN : N.Nonempty := by
    exact ⟨choose e₀,
      Finset.mem_image.mpr ⟨e₀, Finset.mem_univ e₀, rfl⟩⟩
  have hNcard : N.card ≤ q := by
    calc
      N.card ≤ (Finset.univ : Finset E).card :=
        Finset.card_image_le
      _ = Fintype.card E := Finset.card_univ
      _ ≤ q := hCard
  obtain ⟨S, hNS, ⟨J⟩⟩ := hLocal N hN hNcard
  have hChooseS (e : E) : choose e ∈ S :=
    hNS (Finset.mem_image.mpr
      ⟨e, Finset.mem_univ e, rfl⟩)
  letI : Nonempty {i : ι // i ∈ S} :=
    ⟨⟨choose e₀, hChooseS e₀⟩⟩
  have hPairsS :
      ∀ e : E, ∃ j : {i : ι // i ∈ S},
        a e ∈ (setBagPiece (F j.1)).carrier ∧
        b e ∈ (setBagPiece (F j.1)).carrier := by
    intro e
    exact ⟨⟨choose e, hChooseS e⟩,
      (hChoose e).1, (hChoose e).2⟩
  have hUniqueS :
      ∀ j : {i : ι // i ∈ S},
        ∀ e f : E, e ≠ f →
          (a e ∈ (setBagPiece (F j.1)).carrier ∧
           b e ∈ (setBagPiece (F j.1)).carrier) →
          (a f ∈ (setBagPiece (F j.1)).carrier ∧
           b f ∈ (setBagPiece (F j.1)).carrier) → False := by
    intro j e f hef hePair hfPair
    exact hUnique j.1 e f hef hePair hfPair
  exact J.no_cyclic_unique_pairs
    a b e₀ e₁ he hOtherA hOtherB
    hPairsS hUniqueS

end StructuralRamsey.Girth
