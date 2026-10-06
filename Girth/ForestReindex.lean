import Girth.ForestEnumeration

/-! # Relabelling forests

Join trees are frequently restricted or decomposed during leaf induction.
This file packages the trivial but useful fact that the forest condition is
invariant under relabelling by an equivalence.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι κ : Type v}

/-- Pairwise allowed intersections are invariant under an equivalence of the
index type. -/
theorem pairwiseAllowed_reindex
    {F : ι → HypergraphPiece W}
    (h : PairwiseAllowed F)
    (e : κ ≃ ι) :
    PairwiseAllowed (fun k => F (e k)) := by
  intro a b hab
  apply h
  intro heq
  apply hab
  exact e.injective heq

/-- A forest of copies remains a forest after relabelling its index type by an
equivalence.  This includes the empty-family case. -/
theorem ForestOfCopies.reindex
    {F : ι → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (e : κ ≃ ι) :
    ForestOfCopies (fun k => F (e k)) := by
  refine ⟨pairwiseAllowed_reindex hF.pairwiseAllowed e, ?_⟩
  by_cases hN : Nonempty κ
  · letI : Nonempty κ := hN
    letI : Nonempty ι := Nonempty.map e hN
    obtain ⟨J⟩ := hF.joinTree_of_nonempty
    exact Or.inr ⟨J.reindex e⟩
  · left
    exact ⟨fun k => hN ⟨k⟩⟩

end StructuralRamsey.Girth
