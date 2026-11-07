import Girth.TrainFillingColouredOrderedEdgePresentation

set_option Elab.async false

/-!
# From coloured within-predicate order to a global monotone embedding

The coloured one-edge relational language specifies one unary predicate
per colour and the order relation only for pairs in the SAME colour.

To invoke the checked uniqueness of increasing X-placements, one must
also know that the source/target global linear orders concatenate
the colours in their chosen common order. We record these exact
conditions rather than silently assuming that preserving the
within-colour order makes an embedding globally monotone.

Any actual induced relational embedding of these coloured structures
preserves each vertex colour and preserves strict order inside every
colour. If distinct colour blocks appear in common ordered sequence
in source and target, these properties imply global StrictMono.

This is independent of the hypergraph edge relation itself. No
artificial output selected copy or total order is assumed; those
linear orders belong to the actual ordered Ramsey input.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {W V : Type v}
variable [LinearOrder I] [LinearOrder W] [LinearOrder V]

/-- The actual unary relation of a coloured induced embedding forces
its pointwise colour, not only its edge colour word. -/
theorem colouredOrderedEmbedding_preserves_colour
    (k : ℕ) (EW : Set (Set W)) (EV : Set (Set V))
    (sourceColour : W → I) (targetColour : V → I)
    (b : Embedding
      (colouredOrderedEdgeTarget k EW sourceColour)
      (colouredOrderedEdgeTarget k EV targetColour))
    (x : W) :
    targetColour (b x) = sourceColour x := by
  have h := (b.map_rel_iff (.inl (.inr (sourceColour x)))
    (fun _ : Fin 1 => x)).mpr (by
      change sourceColour x = sourceColour x
      rfl)
  change targetColour (b x) = sourceColour x at h
  exact h

/-- An induced embedding preserves all within-colour strict comparisons,
even when the global orders need not yet be compatible across colours. -/
theorem colouredOrderedEmbedding_strictMono_within
    (k : ℕ) (EW : Set (Set W)) (EV : Set (Set V))
    (sourceColour : W → I) (targetColour : V → I)
    (b : Embedding
      (colouredOrderedEdgeTarget k EW sourceColour)
      (colouredOrderedEdgeTarget k EV targetColour))
    (x y : W) (hSame : sourceColour x = sourceColour y)
    (hxy : x < y) :
    b x < b y := by
  have h := (b.map_rel_iff (.inr ()) ![x, y]).mpr (by
    change sourceColour x = sourceColour y ∧ x < y
    exact ⟨hSame, hxy⟩)
  change targetColour (b x) = targetColour (b y) ∧ b x < b y at h
  exact h.2

/-- A block-ordered source and target turn the checked within-colour
order preservation into genuine monotonicity in their complete orders.
The source block property is only used for DIFFERENT colours; there is
no redundant monotonicity assumption on the embedding itself. -/
theorem colouredOrderedEmbedding_strictMono
    (k : ℕ) (EW : Set (Set W)) (EV : Set (Set V))
    (sourceColour : W → I) (targetColour : V → I)
    (b : Embedding
      (colouredOrderedEdgeTarget k EW sourceColour)
      (colouredOrderedEdgeTarget k EV targetColour))
    (hSourceBlocks : ∀ x y : W, sourceColour x ≠ sourceColour y →
      x < y → sourceColour x < sourceColour y)
    (hTargetBlocks : ∀ x y : V,
      targetColour x < targetColour y → x < y) :
    StrictMono b := by
  intro x y hxy
  by_cases hSame : sourceColour x = sourceColour y
  · exact colouredOrderedEmbedding_strictMono_within k EW EV
      sourceColour targetColour b x y hSame hxy
  · have hColour : sourceColour x < sourceColour y :=
      hSourceBlocks x y hSame hxy
    apply hTargetBlocks
    rw [colouredOrderedEmbedding_preserves_colour
          k EW EV sourceColour targetColour b x,
        colouredOrderedEmbedding_preserves_colour
          k EW EV sourceColour targetColour b y]
    exact hColour

end StructuralRamsey.Girth
