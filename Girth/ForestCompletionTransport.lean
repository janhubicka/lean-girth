import Girth.ForestCompletionWitness
import Girth.ForestImage

/-! # Transporting designated forest completions

The circulation picture step transports an old completion forest along an
embedding of an old standard picture into its fresh copy.  Because the
support-piece images preserve forests and one-edge auxiliaries, a completion
witness transports whenever designated status transports with it.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Z N K : Type v}

/-- An injective image of a designated completion witness is a completion
witness for the image of the tested family, provided designated members
remain designated under transport. -/
theorem ForestCompletionWitness.map
    [Fintype K]
    {selected : N → HypergraphPiece W}
    {designated : HypergraphPiece W → Prop}
    {family : K → HypergraphPiece W}
    (h : ForestCompletionWitness selected designated family)
    (φ : W ↪ Z)
    (designated' : HypergraphPiece Z → Prop)
    (hDesignated :
      ∀ F : HypergraphPiece W, designated F →
        designated' (F.map φ)) :
    ForestCompletionWitness
      (fun n : N => (selected n).map φ)
      designated'
      (fun k : K => (family k).map φ) := by
  rcases h with ⟨hForest, hSelected, hClassified⟩
  refine ⟨hForest.map φ, ?_, ?_⟩
  · intro n
    obtain ⟨k, hk⟩ := hSelected n
    exact ⟨k, congrArg (fun F : HypergraphPiece W => F.map φ) hk⟩
  · intro k
    rcases hClassified k with ⟨n, hn⟩ | hOK
    · exact Or.inl
        ⟨n, congrArg (fun F : HypergraphPiece W => F.map φ) hn⟩
    · exact Or.inr (hDesignated (family k) hOK)

/-- One-edge auxiliary members remain eligible for deletion after
transporting an old local forest into a standard picture. -/
theorem mapped_auxiliary_oneEdge
    (φ : W ↪ Z)
    (F : K → HypergraphPiece W)
    (auxiliary : Set K)
    (hAuxiliary :
      ∀ k : K, k ∈ auxiliary → (F k).IsOneEdge) :
    ∀ k : K, k ∈ auxiliary → ((F k).map φ).IsOneEdge := by
  intro k hk
  exact (F k).map_isOneEdge φ (hAuxiliary k hk)

end StructuralRamsey.Girth
