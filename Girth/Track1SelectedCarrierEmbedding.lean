import Girth.Track1FullSelectedOrderedLifts
import Girth.Track1OwnerSplitCoverage

/-!
# Numbered Track 1: restrict true ordered selected embeddings to covered carrier

The full owner-token type contains unused edge tags.  The actual
coloured Ramsey witness has as vertices ONLY those occurring in
the lifted selected B-copies; all its physical edges are contained
in this carrier by the previously established coverage lemma.

A genuine full induced coloured ordered B embedding into the entire
owner-token structure factors through this induced restriction,
because every vertex of that selected image belongs to the
selectedLiftCarrier by construction.

This is not a claim that the whole output is covered by an arbitrary
collection of nonselected tags. It provides the exact selected-copy
part of the final witness restriction.

STAGED DRAFT; no exact-head Lean compiler check yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {V I W Choice : Type v}

namespace ColouredEdgeOwnerSplit

/-- Exactly the union of the lifted *selected* B-copy carriers.
The choice index is independent of the old unary predicate type. -/
def selectedLiftCarrierFor
    (H : ColouredEdgeOwnerSplit V I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H) :
    Set H.Vertex :=
  {z | ∃ c : Choice, z ∈ Set.range (selected c).lift}

/-- The owner-split selected B image, now as a full relational embedding
into the ACTUAL vertex carrier: the union of selected lifted B-copies. -/
noncomputable def actualSelectedEmbeddingOnCarrier
    (H : ColouredEdgeOwnerSplit V I)
    [LinearOrder V] [LinearOrder W]
    (o : LinearOrder H.Vertex)
    (hProjectionOrder : ∀ a b : H.Vertex,
      H.project a < H.project b → @LT.lt H.Vertex o.toLT a b)
    (k : ℕ) (sourceColour : W → I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (c : Choice)
    (oldEmb : RelStructure.Embedding
      (colouredOrderedEdgeTarget k (selected c).sourceEdges sourceColour)
      (colouredOrderedEdgeTarget k H.edges H.predicate))
    (hMatch : ∀ w : W, oldEmb w = (selected c).embedding w)
    (hMono : StrictMono (selected c).embedding) :
    RelStructure.Embedding
      (colouredOrderedEdgeTarget k (selected c).sourceEdges sourceColour)
      ((@colouredOrderedEdgeTarget I H.Vertex k
        H.splitPhysicalEdges H.newPredicate o).induce
        (H.selectedLiftCarrierFor selected)) := by
  classical
  letI : LinearOrder H.Vertex := o
  letI : Preorder H.Vertex := o.toPreorder
  let e := ownerSplit_lifted_colouredOrderedEmbedding
    (selected c) sourceColour oldEmb hMatch hMono hProjectionOrder
  refine {
    toFun := fun w =>
      ⟨e w, ⟨c, ⟨w, rfl⟩⟩⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R x
      exact e.map_rel_iff R x
  }

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.actualSelectedEmbeddingOnCarrier

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
