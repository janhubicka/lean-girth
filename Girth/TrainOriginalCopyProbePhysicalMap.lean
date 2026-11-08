import Girth.TrainPhysicalMapLocalPieces
import Girth.TrainOldCopyLocalProbePieces
import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: old selected-copy probes become ACTUAL output local pieces

These two compositions avoid a hidden whole-cycle pullback:
the original output length-two cycle may have its OTHER source
label in a DIFFERENT actual standard. Only the designated
ORIGINAL B-copy and its two boundary endpoints must come from
one old standard.

The already checked old two-vertex edge and two-edge wagon
probe theorems force a real OLD ShortPiece or LongPiece of the
original selected B-copy, provided a genuine old physical
pair edge or same-wagon no-pair two-edge span exists. The old
source SupremeCycleBound at cutoff >=2 suffices.

For mixed vertex/wagon boundaries, old SupremeCycleBound at
positive cutoff gives OrderOneData.Bound; any genuine old
physical edge through the vertex with that wagon as parent
forces an OLD bridge inside the selected copy.

The literal physical standard map then transports each piece
to the actual output while preserving the ORIGINAL designated
source label and physical wagon. This does NOT claim the old
probe edge(s) exist automatically from the lower witness.
That is the precise remaining trace-reflection obligation.

No appendix / manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v w
namespace LiteralPhysicalMap

variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P}
variable {H : OrderOneData V' E' I' P'}
variable (M : LiteralPhysicalMap D H)

/-- Old source selected-copy order-two girth plus a genuine old
edge/wagon probe yields a true OUTPUT local short-or-long of the
mapped ORIGINAL selected copy, even if the other output source
label belongs to another standard. -/
theorem original_copy_local_piece_map_of_old_two_vertex_probe
    {qcut : ℕ} (hq : 2 ≤ qcut)
    (hOld : D.SupremeCycleBound qcut)
    (i : I) (x y : V)
    (hxy : x ≠ y)
    (hx : x ∈ D.copyCarrier i)
    (hy : y ∈ D.copyCarrier i)
    (hProbe :
      D.PairEdge x y ∨
      (¬ D.PairEdge x y ∧
        ∃ (p : P) (e f : E),
          D.parent e = p ∧ D.parent f = p ∧
          x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f)) :
    H.ShortPiece (M.mapLabel (Sum.inl i))
        (M.mapConnector (Sum.inl x))
        (M.mapConnector (Sum.inl y)) ∨
    H.LongPiece (M.mapLabel (Sum.inl i))
        (M.mapConnector (Sum.inl x))
        (M.mapConnector (Sum.inl y)) := by
  have hPiece :=
    D.copy_local_piece_of_pair_or_wagon_probe
      hq hOld i x y hxy hx hy hProbe
  exact M.localPiece_map (Sum.inl i) (Sum.inl x) (Sum.inl y) hPiece

/-- Old source positive order-one girth plus a true physical
old bridge-edge probe yields an OUTPUT physical ShortPiece of
the exact mapped ORIGINAL B-copy label at mixed boundaries.
There is no need to know the other source label in the old system. -/
theorem original_copy_short_map_of_old_mixed_bridge_probe
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : D.SupremeCycleBound qcut)
    (i : I) (x : V) (p : P)
    (hx : x ∈ D.copyCarrier i)
    (hMeets : D.Meets (Sum.inl i) p)
    (e : E) (hParent : D.parent e = p)
    (hXE : x ∈ D.edgeCarrier e) :
    H.ShortPiece (M.mapLabel (Sum.inl i))
      (M.mapConnector (Sum.inl x))
      (M.mapConnector (Sum.inr p)) := by
  have hLocal : D.LocalPieceSystemBound 1 := by
    intro n C hAcc hOrd
    exact D.localPieceSystemBound_of_supremeCycleBound
      qcut hOld n C hAcc (by omega)
  have hBound : D.Bound := D.bound_of_localPieceSystemBound hLocal
  have hPiece : D.ShortPiece (Sum.inl i)
      (Sum.inl x) (Sum.inr p) :=
    D.copy_mixed_bridge_of_old_physical_probe
      hBound i x p hx hMeets e hParent hXE
  exact M.shortPiece_map_local
    (Sum.inl i) (Sum.inl x) (Sum.inr p) hPiece


/-- The EXACT mixed source-length-two original-copy transport.
The target original selected copy owns a genuine OLD edge t,
establishing its old wagon; the gluing witness supplies a TRUE
old shared edge s through the boundary vertex x. If their
physical output images have the same real wagon, injectivity of
the standard wagon embedding reflects the old wagon equality.
The old order-one bound then forces a bridge in the ORIGINAL
selected copy i. It maps to a legal physical OUTPUT ShortPiece.

Unlike a mistaken label-provenance argument, this proof never
identifies the selected original B-copy with the reduced witness
standard, and retains the exact wagon parent quotient. -/
theorem original_copy_short_map_of_shared_wagon_contact
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : D.SupremeCycleBound qcut)
    (i : I) (x : V)
    (shared selectedEdge : E)
    (hx : x ∈ D.copyCarrier i)
    (hSelected : selectedEdge ∈ D.copyEdges i)
    (hSharedX : x ∈ D.edgeCarrier shared)
    (hSameOutputParent :
      H.parent (M.edge shared) = H.parent (M.edge selectedEdge)) :
    H.ShortPiece (M.mapLabel (Sum.inl i))
      (M.mapConnector (Sum.inl x))
      (M.mapConnector (Sum.inr (D.parent selectedEdge))) := by
  have hLocal : D.LocalPieceSystemBound 1 := by
    intro n C hAccept hOrder
    exact D.localPieceSystemBound_of_supremeCycleBound
      qcut hOld n C hAccept (by omega)
  have hBound : D.Bound := D.bound_of_localPieceSystemBound hLocal
  have hOldParent : D.parent shared = D.parent selectedEdge :=
    M.source_parent_eq_of_output_parent_eq
      shared selectedEdge hSameOutputParent
  obtain ⟨bridge, hBridgeMem, hBridgeParent, hBridgeX⟩ :=
    D.copy_bridge_of_old_shared_wagon_edge
      hBound i x shared selectedEdge hx hSelected
      hSharedX hOldParent
  have hPiece : D.ShortPiece (Sum.inl i)
      (Sum.inl x) (Sum.inr (D.parent selectedEdge)) :=
    ⟨bridge, hBridgeMem, hBridgeX,
      ⟨bridge, rfl, hBridgeParent⟩⟩
  exact M.shortPiece_map_local
    (Sum.inl i) (Sum.inl x)
    (Sum.inr (D.parent selectedEdge)) hPiece

end LiteralPhysicalMap
end StructuralRamsey.Girth.OrderOneData
