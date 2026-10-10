import Girth.ActiveBoundary
import Girth.ForestDistinctBoundaryAllowed

/-!
# A genuine B-copy's complete A-support has the whole-edge boundary

The relational active-boundary theorem identifies a boundary with
the carrier of an A-copy inside the selected B-copy. For the forest
increment it is not enough to know that the boundary is such a
carrier: that edge must actually belong to the selected B-piece's
OWN A-support, and it must be an edge of the local support K.

We represent the complete support explicitly by the image carriers
of all A-embeddings into B. The own-support membership is then
definitional. The only remaining geometric input is the membership
of the classified boundary copy in the local K.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W : Type v}

/-- Complete A-support of one embedded relational B-copy, as a
hypergraph piece on the ambient vertex set. -/
def embeddedACopySupportPiece
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L W}
    (b : RelStructure.Embedding B D) :
    HypergraphPiece W where
  carrier := copyCarrier b
  edges := {e | ∃ a : RelStructure.Embedding A B,
    e = copyCarrier (b.comp a)}
  edge_subset_carrier := by
    intro e he z hz
    obtain ⟨a, rfl⟩ := he
    obtain ⟨x, hx⟩ := hz
    exact ⟨a x, hx⟩

@[simp] theorem embeddedACopySupportPiece_carrier
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L W}
    (b : RelStructure.Embedding B D) :
    (embeddedACopySupportPiece A b).carrier = copyCarrier b := rfl

/-- A small-or-embedded-A-copy relational boundary translates to the
exact small-or-whole-edge boundary of the selected hypergraph piece.
Unlike a carrier-only statement, this certifies the selected member's
OWN support-edge membership. -/
theorem embeddedACopySupportPiece_smallOrWholeBoundary
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L W}
    (b : RelStructure.Embedding B D)
    (S : Set W) (K : Set (Set W))
    (hClassify :
      (copyCarrier b ∩ S).Subsingleton ∨
        ∃ a : RelStructure.Embedding A B,
          copyCarrier b ∩ S = copyCarrier (b.comp a))
    (hLocal :
      ∀ a : RelStructure.Embedding A B,
        copyCarrier b ∩ S = copyCarrier (b.comp a) →
        copyCarrier (b.comp a) ∈ K) :
    SmallOrWholeEdgeBoundary K S (embeddedACopySupportPiece A b) := by
  rcases hClassify with hs | ⟨a, ha⟩
  · exact Or.inl hs
  · exact Or.inr
      ⟨copyCarrier (b.comp a), hLocal a ha,
        ⟨a, rfl⟩, ha⟩

end StructuralRamsey.Girth
