import Girth.TrainColouredOwnerInducedUniformLift
import Girth.TrainColouredOwnerProjectionOrder
import Girth.TrainColouredOwnerExactColourTransfer

/-!
# Numbered Track 1: genuine selected ordered embeddings after edge-owner splitting

Each selected old embedding is an induced embedding of the *complete*
coloured uniform-edge relation and the within-predicate orders.
The checked owner-splitting construction gives a genuine lifted
embedding, not merely an abstract carrier map.

This theorem packages one COMMON projection-first order for the whole
selected family.  It deliberately retains the dependency on actual
old induced embeddings; obtaining those from the EHN selected closure
family is the next adapter. No additional assumptions about
the new embeddings are introduced.

STAGED DRAFT on a separate branch: not kernel-compiled yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v

variable {V I W Choice : Type v}

namespace ColouredEdgeOwnerSplit

/-- All genuinely selected old coloured ordered B-embeddings lift
to full induced coloured ordered embeddings for ONE common order
on the split vertex type.  Edge and predicate relations are
preserved and reflected, and the lift uses the canonical shared
isolated-vertex bottom tag. -/
theorem exists_commonOrder_fullSelectedLifts
    (H : ColouredEdgeOwnerSplit V I)
    [LinearOrder V] [LinearOrder W] [Finite H.Vertex]
    (k : ℕ)
    (sourceColour : W → I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (oldEmb : ∀ c : Choice, RelStructure.Embedding
      (colouredOrderedEdgeTarget k (selected c).sourceEdges sourceColour)
      (colouredOrderedEdgeTarget k H.edges H.predicate))
    (hMatch : ∀ c : Choice, ∀ w : W,
      oldEmb c w = (selected c).embedding w)
    (hMono : ∀ c : Choice, StrictMono (selected c).embedding) :
    ∃ o : LinearOrder H.Vertex,
      ∀ c : Choice,
        ∃ e : RelStructure.Embedding
          (colouredOrderedEdgeTarget k (selected c).sourceEdges sourceColour)
          (@colouredOrderedEdgeTarget I H.Vertex k
            H.splitPhysicalEdges H.newPredicate o),
          ∀ w : W, e w = (selected c).lift w := by
  classical
  obtain ⟨o, ho⟩ := H.exists_projectionFirstLinearOrder
  refine ⟨o, ?_⟩
  intro c
  letI : LinearOrder H.Vertex := o
  letI : Preorder H.Vertex := o.toPreorder
  let e := ownerSplit_lifted_colouredOrderedEmbedding
    (selected c) sourceColour (oldEmb c)
    (hMatch c) (hMono c) ho
  exact ⟨e, fun _ => rfl⟩

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.exists_commonOrder_fullSelectedLifts

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
