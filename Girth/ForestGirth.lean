import Girth.Forest
import Girth.BergeGlue

/-! # Girth along singleton forest attachments

For the untouched subsystems in a Picture step, different standard copies meet
in at most one relevant vertex.  Once the join tree is enumerated by leaf
attachments, girth preservation is just repeated singleton gluing.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Union of the carriers of a finite list of hypergraph pieces. -/
def pieceListCarrier : List (HypergraphPiece W) → Set W
  | [] => ∅
  | F :: Fs => F.carrier ∪ pieceListCarrier Fs

/-- Union of the edge families of a finite list of hypergraph pieces. -/
def pieceListEdges : List (HypergraphPiece W) → Set (Set W)
  | [] => ∅
  | F :: Fs => F.edges ∪ pieceListEdges Fs

/-- Reverse admissible enumeration: the head piece meets the union of all
remaining carriers in at most one vertex, recursively. -/
def SingletonAttachmentList : List (HypergraphPiece W) → Prop
  | [] => True
  | F :: Fs =>
      (F.carrier ∩ pieceListCarrier Fs).Subsingleton ∧
        SingletonAttachmentList Fs

/-- Every edge in the list union lies in the corresponding carrier union. -/
theorem pieceListEdges_subset_carrier
    (Fs : List (HypergraphPiece W))
    {e : Set W} (he : e ∈ pieceListEdges Fs) :
    e ⊆ pieceListCarrier Fs := by
  induction Fs with
  | nil =>
      simpa [pieceListEdges] using he
  | cons F Fs ih =>
      rw [pieceListEdges] at he
      rw [pieceListCarrier]
      rcases he with hF | hFs
      · intro x hx
        exact Or.inl (F.edge_subset hF hx)
      · intro x hx
        exact Or.inr (ih hFs hx)

/-- Girth is preserved under a reverse sequence of singleton attachments. -/
theorem girthGT_pieceList_of_singletonAttachments
    {g : ℕ} (Fs : List (HypergraphPiece W))
    (hAttach : SingletonAttachmentList Fs)
    (hPiece : ∀ F ∈ Fs, GirthGT F.edges g) :
    GirthGT (pieceListEdges Fs) g := by
  induction Fs with
  | nil =>
      intro hcyc
      rcases hcyc with ⟨c, _⟩
      let i : Fin c.length := ⟨0, by omega⟩
      have h := c.edge_mem i
      simpa [pieceListEdges] using h
  | cons F Fs ih =>
      rw [SingletonAttachmentList] at hAttach
      rcases hAttach with ⟨hSep, hTail⟩
      have hF : GirthGT F.edges g :=
        hPiece F (by simp)
      have hFs : GirthGT (pieceListEdges Fs) g := by
        apply ih hTail
        intro G hG
        exact hPiece G (by simp [hG])
      have hcross :
          ∀ ⦃eF eR : Set W⦄,
            eF ∈ F.edges →
            eR ∈ pieceListEdges Fs →
            eF ∩ eR ⊆ F.carrier ∩ pieceListCarrier Fs := by
        intro eF eR heF heR x hx
        exact ⟨F.edge_subset heF hx.1,
          pieceListEdges_subset_carrier Fs heR hx.2⟩
      simpa [pieceListEdges] using
        girthGT_union_of_subsingleton_glue
          hSep hcross hF hFs

end StructuralRamsey.Girth
