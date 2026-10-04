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
      have hpos : 0 < c.length :=
        lt_of_lt_of_le (by decide : 0 < 2) c.hlength
      let i : Fin c.length := ⟨0, hpos⟩
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



/-- Regard a vertex set as the one-edge hypergraph piece whose only edge is
the whole set. -/
def oneEdgePiece (S : Set W) : HypergraphPiece W where
  carrier := S
  edges := {S}
  edge_subset_carrier := by
    intro e he
    have hEq : e = S := by simpa using he
    simpa [hEq]

/-- A one-edge piece has Berge girth above every finite bound. -/
theorem oneEdgePiece_girthGT (S : Set W) (g : ℕ) :
    GirthGT (oneEdgePiece S).edges g := by
  apply girthGT_of_edgeFamily_subsingleton
  intro e he f hf
  simpa [oneEdgePiece] using he.trans hf.symm

/-- A reverse admissible enumeration of sets, each meeting the remaining union
in at most one vertex, has no Berge cycle of length at most g. -/
theorem girthGT_oneEdgeList_of_singletonAttachments
    {g : ℕ} (Ss : List (Set W))
    (hAttach : SingletonAttachmentList (Ss.map oneEdgePiece)) :
    GirthGT (pieceListEdges (Ss.map oneEdgePiece)) g := by
  apply girthGT_pieceList_of_singletonAttachments
    (Ss.map oneEdgePiece) hAttach
  intro F hF
  rcases List.mem_map.mp hF with ⟨S, _hS, rfl⟩
  exact oneEdgePiece_girthGT S g
end StructuralRamsey.Girth
