import Girth.ForestGirth
import Girth.BergeGlue

/-!
# Berge girth along permitted singleton or whole-support-edge attachments

The existing reverse-attachment girth theorem only treats singleton
separator intersections. But the forest definition also permits
gluing over a COMPLETE A-support edge belonging to both pieces.
The elementary Berge-gluing theorems handle both cases.

This module unifies them for any reverse admissible enumeration
of support pieces. No assumptions about the size of ambient vertex
sets or the length/shape of a prior construction are required.

The remaining step for a completely arbitrary ForestOfCopies is
to extract such a reverse enumeration from its join tree.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- A reverse leaf enumeration in which every new piece meets the rest
of the family either in at most one vertex or in exactly one
COMPLETE support edge that belongs to both edge families. -/
def PermittedAttachmentList : List (HypergraphPiece W) → Prop
  | [] => True
  | F :: Fs =>
      ((F.carrier ∩ pieceListCarrier Fs).Subsingleton ∨
        ∃ e : Set W, e ∈ F.edges ∧
          e ∈ pieceListEdges Fs ∧
          F.carrier ∩ pieceListCarrier Fs = e) ∧
      PermittedAttachmentList Fs

/-- Every reverse admissible list of hypergraph pieces preserves an
arbitrary prescribed Berge-girth bound when all individual pieces do.
This simultaneously generalizes singleton and complete A-edge gluing. -/
theorem girthGT_pieceList_of_permittedAttachments
    (Fs : List (HypergraphPiece W)) (g : ℕ)
    (hAttach : PermittedAttachmentList Fs)
    (hPieces : ∀ F ∈ Fs, GirthGT F.edges g) :
    GirthGT (pieceListEdges Fs) g := by
  induction Fs with
  | nil =>
      intro hBad
      rcases hBad with ⟨c, _⟩
      have hLen : 0 < c.length := by omega
      have hImpossible := c.edge_mem (⟨0, hLen⟩ : Fin c.length)
      simpa [pieceListEdges] using hImpossible
  | cons F Fs ih =>
      obtain ⟨hSeparator, hTail⟩ := hAttach
      have hF : GirthGT F.edges g :=
        hPieces F (by simp)
      have hRest : GirthGT (pieceListEdges Fs) g := by
        apply ih hTail
        intro P hP
        exact hPieces P (by simp [hP])
      have hCross :
          ∀ ⦃eF eR : Set W⦄,
            eF ∈ F.edges → eR ∈ pieceListEdges Fs →
            eF ∩ eR ⊆ F.carrier ∩ pieceListCarrier Fs := by
        intro eF eR heF heR x hx
        exact ⟨F.edge_subset heF hx.1,
          pieceListEdges_subset_carrier Fs heR hx.2⟩
      rcases hSeparator with hSmall | ⟨separator, heF, heRest, hEq⟩
      · simpa [pieceListEdges] using
          (girthGT_union_of_subsingleton_glue
            (S := F.carrier ∩ pieceListCarrier Fs)
            hSmall hCross hF hRest)
      · have hCrossEdge :
            ∀ ⦃eF eR : Set W⦄,
              eF ∈ F.edges → eR ∈ pieceListEdges Fs →
              eF ∩ eR ⊆ separator := by
          intro eF eR hEF hER
          rw [← hEq]
          exact hCross hEF hER
        simpa [pieceListEdges] using
          (girthGT_union_of_edge_glue
            (separator := separator)
            heF heRest hCrossEdge hF hRest)

/-- The old singleton-attachment hypothesis is a special case of
the more general permitted-separator enumeration. -/
theorem singletonAttachmentList_implies_permitted
    (Fs : List (HypergraphPiece W))
    (h : SingletonAttachmentList Fs) :
    PermittedAttachmentList Fs := by
  induction Fs with
  | nil => trivial
  | cons F Fs ih =>
      exact ⟨Or.inl h.1, ih h.2⟩

end StructuralRamsey.Girth
