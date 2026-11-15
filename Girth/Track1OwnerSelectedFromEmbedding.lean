import Girth.TrainColouredOwnerSelectedLift

/-!
# Track 1: canonical selected owner-split data from an actual embedding

The earlier owner-split API expects ColouredOwnerSelectedCopy.  This
constructor builds that record directly from an injected vertex map,
the genuine edge-image membership, and the source forbidden-part
degree-one hypothesis. No independent choice of edge labels is made:
the old physical edge is exactly the image carrier of the source edge.

This is an interface lemma; the old EHN selected family must provide
the edge and forbidden-degree hypotheses through its actual embedding.

DRAFT / UNCOMPILED.
-/

namespace StructuralRamsey.Girth

universe v

namespace ColouredOwnerSelectedCopy

variable {V I W : Type v}

/-- Actual old support-edge membership determines the selected physical
edge map uniquely, without any added edge tags or free choice. -/
def ofEdgeEmbedding
    (H : ColouredEdgeOwnerSplit V I)
    (sourceEdges : Set (Set W))
    (b : W ↪ V)
    (hEdges : ∀ e : Set W, e ∈ sourceEdges → b '' e ∈ H.edges)
    (hForbidden : ∀ (w : W)
      (e f : {e : Set W // e ∈ sourceEdges}),
      H.predicate (b w) ∉ H.allowed →
      w ∈ e.1 → w ∈ f.1 → e = f) :
    ColouredOwnerSelectedCopy (W := W) H where
  sourceEdges := sourceEdges
  embedding := b
  physicalEdge := fun e => ⟨b '' e.1, hEdges e.1 e.2⟩
  edge_image := fun _ => rfl
  forbidden_unique := hForbidden

#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.ofEdgeEmbedding

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
