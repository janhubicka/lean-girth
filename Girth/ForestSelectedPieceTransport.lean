import Girth.ForestRelationalAttachmentCompletion

/-!
# Selected A/B support pieces: standard copies or local core edges

The circulation proof selects from designated B-copies and copies of A.
Every selected piece must be assigned to one local gluing owner. There
are two relevant cases for the actual free picture attachment:

* A selected piece already belongs to a full standard picture and is
  the image of an old tested piece (either an A-copy or designated B-copy).
* A selected A-support edge is in the new core; the local-forest witness
  assigns it to a gluing copy, so it is a one-edge piece of that gluing
  support. Factorization through the standard copy transports it from
  an old tested A-edge.

This file proves the exact case-split-to-TransportedPiece implication.
It does NOT claim the classification automatically: proving it for
the actual selected family of the picture step is the next local
ownership obligation of the full circulation proposition.
-/

namespace StructuralRamsey.Girth

universe v
variable {Src Old W Q N : Type v}

/-- A single selected A/B support piece has an exact old-picture
preimage if it is either a transported old tested piece or a local
gluing A-edge whose source active A-edge is tested. -/
theorem selectedPiece_transported_of_standard_or_gluing
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : StrongSupportEmbedding H K)
    (active : Src ↪ Old) (standard : Old ↪ W)
    (hFactor : ∀ x : Src, outer x = standard (active x))
    (testedOld : HypergraphPiece Old → Prop)
    (hTestActiveEdge :
      ∀ e : Set Src, e ∈ H →
        testedOld (HypergraphPiece.oneEdge (active '' e)))
    (T : HypergraphPiece W)
    (hClassify :
      (∃ R : HypergraphPiece Old,
        testedOld R ∧ T = R.map standard) ∨
      (∃ e : Set W, e ∈ outer.supportPiece.edges ∧
        T = HypergraphPiece.oneEdge e)) :
    TransportedPiece testedOld standard T := by
  rcases hClassify with ⟨R, hTest, hImage⟩ | ⟨e, he, hImage⟩
  · exact ⟨R, hTest, hImage⟩
  · rw [hImage]
    exact outer.oneEdge_transported_of_factor
      active standard hFactor testedOld hTestActiveEdge e he

/-- The family-level classification produces exactly the
selected-piece transport hypothesis used by the verified
forest-completion assembly. Its owner map need not be injective:
reindexing the DISTINCT local owners is handled separately. -/
theorem selectedFamily_transported_of_standard_or_gluing
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : Q → StrongSupportEmbedding H K)
    (active : Q → Src ↪ Old)
    (standard : Q → Old ↪ W)
    (hFactor : ∀ q (x : Src),
      outer q x = standard q (active q x))
    (testedOld : HypergraphPiece Old → Prop)
    (hTestActiveEdge :
      ∀ q (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active q) '' e)))
    (owner : N → Q)
    (selected : N → HypergraphPiece W)
    (hClassify :
      ∀ n : N,
        (∃ R : HypergraphPiece Old,
          testedOld R ∧ selected n = R.map (standard (owner n))) ∨
        (∃ e : Set W,
          e ∈ (outer (owner n)).supportPiece.edges ∧
          selected n = HypergraphPiece.oneEdge e)) :
    ∀ n : N,
      TransportedPiece testedOld (standard (owner n)) (selected n) := by
  intro n
  exact selectedPiece_transported_of_standard_or_gluing
    (outer (owner n)) (active (owner n)) (standard (owner n))
    (hFactor (owner n)) testedOld (hTestActiveEdge (owner n))
    (selected n) (hClassify n)

end StructuralRamsey.Girth
