import Girth.ForestMixedSetBound
import Girth.ForestAllSupportGirth
import Girth.ForestGirth
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Ordinary girth from the finite-set forest property of physical one-edge members

A cyclic family of at most q distinct physical edges is a finite family
of distinct one-edge support pieces. The honest FiniteMixedForestThrough
hypothesis applies to the FINITE IMAGE of those pieces, not to an
arbitrary list of possibly repeated B-support labels.

The checked union-girth theorem for genuine join-tree forests then
contradicts the original Berge cycle. This is the missing generic
conversion behind the circulation statement that bottom mixed forests
automatically give ordinary physical-edge girth. Its application to the
selected A/B-tested predicate still requires identifying its literal
one-edge constructor; nothing is assumed about the recursive witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Bounded foresthood for all finite sets of actual one-edge members
forces the entire ambient hypergraph to have Berge girth above the same
cutoff. The property is stated using the literal one-edge pieces of
ForestGirth, without injecting arbitrary duplicate support labels. -/
theorem girthGT_of_finiteOneEdgeForest
    (H : Set (Set W)) (q : ℕ)
    (hFinite : FiniteMixedForestThrough
      (fun F : HypergraphPiece W =>
        ∃ e : Set W, e ∈ H ∧ F = oneEdgePiece e) q) :
    GirthGT H q := by
  classical
  rintro ⟨C, hBound⟩
  let pieces : Fin C.length → HypergraphPiece W :=
    fun i => oneEdgePiece (C.edge i)
  have hTest : ∀ i, ∃ e : Set W, e ∈ H ∧ pieces i = oneEdgePiece e := by
    intro i
    exact ⟨C.edge i, C.edge_mem i, rfl⟩
  have hCount : Fintype.card (Fin C.length) ≤ q := by
    simpa using hBound
  let PieceIndex := {F : HypergraphPiece W // F ∈ finitePieceImage pieces}
  have hForest : ForestOfCopies (fun p : PieceIndex => p.val) :=
    FiniteMixedForestThrough.image
      (fun F : HypergraphPiece W =>
        ∃ e : Set W, e ∈ H ∧ F = oneEdgePiece e)
      q hFinite pieces hTest hCount
  have hEach (p : PieceIndex) : GirthGT (p.val).edges q := by
    have hMem : p.val ∈ Finset.univ.image pieces := by
      simpa [finitePieceImage] using p.property
    obtain ⟨i, _hi, hp⟩ := Finset.mem_image.mp hMem
    have heq : p.val = oneEdgePiece (C.edge i) := hp.symm
    rw [heq]
    exact oneEdgePiece_girthGT (C.edge i) q
  have hUnion : GirthGT
      (⋃ p : PieceIndex, (p.val).edges) q :=
    girthGT_union_of_forest (fun p : PieceIndex => p.val)
      hForest q hEach
  let lifted : BergeCycle (⋃ p : PieceIndex, (p.val).edges) := {
    length := C.length
    hlength := C.hlength
    edge := C.edge
    vertex := C.vertex
    edge_mem := by
      intro i
      refine Set.mem_iUnion.mpr ⟨⟨pieces i, ?_⟩, ?_⟩
      · change pieces i ∈ finitePieceImage pieces
        simp [finitePieceImage]
      · change C.edge i ∈ (pieces i).edges
        simp [pieces, oneEdgePiece]
    edge_injective := C.edge_injective
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem
  }
  exact hUnion ⟨lifted, hBound⟩

end StructuralRamsey.Girth
