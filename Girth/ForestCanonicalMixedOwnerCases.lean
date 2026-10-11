import Girth.ForestMixedOwnerChoice
import Girth.ForestCanonicalTransport

/-!
# Eliminate the regular-owner carrier hypothesis by exact support transport

The circulation mixed-owner interface asks whether every selected
member can be assigned to either a genuine full standard picture or
one ambient core edge. A regular owner's "tested" predicate is most
naturally the canonical image of an old tested support piece, not a
new independent property.

For that canonical definition, membership of a selected support
piece in a full standard picture is AUTOMATIC: every transported
piece has carrier inside the image of the old picture. Thus the
regular branch of MixedOwnerSelectionCertificate needs only an
old tested preimage and the exact small-or-whole boundary theorem;
no separate carrier containment assumption is necessary.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old W Q E : Type v}

/-- Any piece with an old support-piece preimage under a standard
embedding has carrier inside the image of that embedding. -/
theorem TransportedPiece.carrier_subset_standardRange
    (testedOld : HypergraphPiece Old → Prop)
    (φ : Old ↪ W) (T : HypergraphPiece W)
    (hT : TransportedPiece testedOld φ T) :
    T.carrier ⊆ Set.range φ := by
  obtain ⟨R, _hOld, rfl⟩ := hT
  rintro x hx
  change x ∈ φ '' R.carrier at hx
  obtain ⟨y, _hy, hxy⟩ := hx
  exact ⟨y, hxy⟩

/-- The meaningful regular/exceptional case distinction: either
one tested old support piece transports under a full standard
embedding AND its local boundary is legal, or the selected piece
is literally an ambient core edge. Carrier containment is derived. -/
theorem mixedOwnerCertificate_of_canonicalCases
    (full : Q → HypergraphPiece W)
    (std : Q → Old ↪ W)
    (hFullCarrier : ∀ q, (full q).carrier = Set.range (std q))
    (coreEdge : E → Set W)
    (S : Set W) (K : Set (Set W))
    (testedOld : HypergraphPiece Old → Prop)
    (T : HypergraphPiece W)
    (hCase :
      (∃ q : Q,
        TransportedPiece testedOld (std q) T ∧
          SmallOrWholeEdgeBoundary K S T) ∨
      (∃ e : E, T = HypergraphPiece.oneEdge (coreEdge e))) :
    ∃ o : Q ⊕ E,
      MixedOwnerSelectionCertificate T full coreEdge S K
        (fun q U => TransportedPiece testedOld (std q) U) o := by
  rcases hCase with ⟨q, hOld, hBoundary⟩ | ⟨e, he⟩
  · refine ⟨Sum.inl q, ?_⟩
    change T.carrier ⊆ (full q).carrier ∧
      TransportedPiece testedOld (std q) T ∧
      SmallOrWholeEdgeBoundary K S T
    refine ⟨?_, hOld, hBoundary⟩
    rw [hFullCarrier q]
    exact TransportedPiece.carrier_subset_standardRange
      testedOld (std q) T hOld
  · exact ⟨Sum.inr e, he⟩

/-- Pointwise canonical classifications supply the exact owner
certificate family required by the conditional mixed increment.
Only geometric boundary information remains in the regular branch. -/
theorem mixedOwnerFamilyCases_of_canonicalTransport
    {N : Type v}
    (full : Q → HypergraphPiece W)
    (std : Q → Old ↪ W)
    (hFullCarrier : ∀ q, (full q).carrier = Set.range (std q))
    (coreEdge : E → Set W)
    (S : Set W) (K : Set (Set W))
    (testedOld : HypergraphPiece Old → Prop)
    (selected : N → HypergraphPiece W)
    (hCases : ∀ n : N,
      (∃ q : Q,
        TransportedPiece testedOld (std q) (selected n) ∧
          SmallOrWholeEdgeBoundary K S (selected n)) ∨
      (∃ e : E, selected n = HypergraphPiece.oneEdge (coreEdge e))) :
    ∀ n : N, ∃ o : Q ⊕ E,
      MixedOwnerSelectionCertificate (selected n) full coreEdge
        S K (fun q U => TransportedPiece testedOld (std q) U) o := by
  intro n
  exact mixedOwnerCertificate_of_canonicalCases
    full std hFullCarrier coreEdge S K testedOld (selected n) (hCases n)

end StructuralRamsey.Girth
