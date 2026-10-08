import Girth.ForestMarkedCarrierContacts
import Girth.Forest
import Mathlib.Tactic

/-!
# Finite marked tests for actual allowed B-copy intersections

An induced support piece contains every ambient support edge entirely
contained in its carrier. Under this saturation condition, a new
piece's allowed intersection with an old piece is decided by the
vertex intersection and the *new* piece's support edges.

Hence finite marked carrier masks, not the number of old B-copies,
suffice to check pairwise allowed intersections of one new B-copy
against an arbitrarily large old designated family.

This is not a join-tree theorem and does not certify the whole
forest property: global running intersections remain separate.
-/

namespace StructuralRamsey.Girth

universe v u
variable {W : Type v}

/-- An induced ambient support piece contains every old support edge
whose entire vertex set is inside its carrier. -/
def HypergraphPiece.EdgesSaturated
    (E : Set (Set W)) (D : HypergraphPiece W) : Prop :=
  ∀ ⦃e : Set W⦄, e ∈ E → e ⊆ D.carrier → e ∈ D.edges

/-- A test depending only on the actual intersection with the new piece,
using its own support edges as the permitted large separators. -/
def NewPieceOverlapAllowed
    (P : HypergraphPiece W) (S : Set W) : Prop :=
  S.Subsingleton ∨ ∃ e ∈ P.edges, S = e

/-- For an old induced piece, the symmetric edge-membership condition
from AllowedIntersection is automatic once an intersection is a support
edge of the new piece. -/
theorem allowedIntersection_iff_newPieceOverlapAllowed
    (E : Set (Set W)) (P D : HypergraphPiece W)
    (hNewEdges : P.edges ⊆ E)
    (hOldSat : D.EdgesSaturated E) :
    AllowedIntersection P D ↔
      NewPieceOverlapAllowed P (P.carrier ∩ D.carrier) := by
  constructor
  · intro h
    rcases h with hSmall | ⟨e, heP, _, hEq⟩
    · exact Or.inl hSmall
    · exact Or.inr ⟨e, heP, hEq⟩
  · intro h
    rcases h with hSmall | ⟨e, heP, hEq⟩
    · exact Or.inl hSmall
    · right
      have heSubset : e ⊆ D.carrier := by
        intro x hx
        have hi : x ∈ P.carrier ∩ D.carrier := by
          rw [hEq]
          exact hx
        exact hi.2
      exact ⟨e, heP, hOldSat (hNewEdges heP) heSubset, hEq⟩

/-- Equal overlaps with two induced old pieces yield the same
AllowedIntersection answer for the new piece. -/
theorem allowedIntersection_congr_of_sameOverlap
    (E : Set (Set W)) (P D R : HypergraphPiece W)
    (hNewEdges : P.edges ⊆ E)
    (hSatD : D.EdgesSaturated E)
    (hSatR : R.EdgesSaturated E)
    (hSame : P.carrier ∩ D.carrier = P.carrier ∩ R.carrier) :
    AllowedIntersection P D ↔ AllowedIntersection P R := by
  rw [allowedIntersection_iff_newPieceOverlapAllowed E P D hNewEdges hSatD,
    allowedIntersection_iff_newPieceOverlapAllowed E P R hNewEdges hSatR]
  rw [hSame]

/-- Forget the internal edge labels of old designated pieces when
constructing their finite marked carrier masks. -/
def oldPieceCarriers (family : Set (HypergraphPiece W)) :
    Set (Set W) :=
  {C | ∃ D ∈ family, D.carrier = C}

/-- For one marked new piece, pairwise AllowedIntersection with every
old designated induced piece is equivalent to testing one realised
carrier per marked-vertex mask. The finite representatives are actual
old carriers but are not separately given arbitrary new edge sets. -/
theorem allAllowedIntersections_iff_markedRepresentatives
    {I : Type u} [Fintype I]
    (E : Set (Set W))
    (P : HypergraphPiece W)
    (family : Set (HypergraphPiece W))
    (f : I → W) (S : Set I)
    (hPorts : P.carrier = f '' S)
    (hNewEdges : P.edges ⊆ E)
    (hOldSat : ∀ D ∈ family, D.EdgesSaturated E) :
    (∀ D ∈ family, AllowedIntersection P D) ↔
      (∀ R ∈ markedCarrierRepresentatives
          (oldPieceCarriers family) f,
        NewPieceOverlapAllowed P (P.carrier ∩ R)) := by
  have hCarriers :
      (∀ D ∈ family, AllowedIntersection P D) ↔
        (∀ C ∈ oldPieceCarriers family,
          NewPieceOverlapAllowed P (P.carrier ∩ C)) := by
    constructor
    · intro hAll C hC
      obtain ⟨D, hD, rfl⟩ := hC
      exact (allowedIntersection_iff_newPieceOverlapAllowed
        E P D hNewEdges (hOldSat D hD)).mp (hAll D hD)
    · intro hMasks D hD
      exact (allowedIntersection_iff_newPieceOverlapAllowed
        E P D hNewEdges (hOldSat D hD)).mpr
        (hMasks D.carrier ⟨D, hD, rfl⟩)
  have hFinite :
      (∀ C ∈ oldPieceCarriers family,
        NewPieceOverlapAllowed P (P.carrier ∩ C)) ↔
      (∀ R ∈ markedCarrierRepresentatives
          (oldPieceCarriers family) f,
        NewPieceOverlapAllowed P (P.carrier ∩ R)) :=
    freshCarrier_allContacts_iff_representatives
      (oldPieceCarriers family) f S P.carrier
      (NewPieceOverlapAllowed P) (by
        intro C hC
        rw [hPorts])
  exact hCarriers.trans hFinite

/-- The number of old carriers needed to certify pairwise allowed
overlaps is bounded by the number of subsets of marked positions,
independent of the number of old B-copies. -/
theorem allowedIntersectionRepresentative_card_le
    {I : Type u} [Fintype I]
    (family : Set (HypergraphPiece W)) (f : I → W) :
    (markedCarrierRepresentatives (oldPieceCarriers family) f).card ≤
      Fintype.card (Finset I) :=
  markedCarrierRepresentatives_card_le (oldPieceCarriers family) f

end StructuralRamsey.Girth
