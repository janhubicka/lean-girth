import Girth.TrainTwoCopyLocalSymmetry
import Girth.TrainTwoCopyVertexProbe
import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a true lower witness copy gets a local piece against
either a DIFFERENT copy label or a physical A-edge label

The original length-two selected-cycle reduction cannot assume
the shadow of its OTHER original source label is a designated
witness gluing copy. It may instead be a genuine CORE A-edge.

At order two, provided x,y are DISTINCT true shared core
vertices, both incident with the lower gluing copy i and
with a second genuinely different lower label a, the checked
two-copy symmetry theorem (a is designated) or physical edge
probe (a is a real A-edge) gives a local short-or-long piece
in i. No assertion about the original selected B-label is
made: that still requires old-standard trace reflection and
the old-copy local probe.

For mixed vertex/wagon boundaries the CHECKED order-one bridge
theorem similarly gives a real bridge through x,p belonging to
the chosen lower gluing copy i, regardless of the other label's
sort. This retains the exact physical witness edge and wagon.
No appendix / manuscript changes.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In a lower witness with local order-two system girth, a
designated gluing copy sharing two DISTINCT vertex connectors
with any different label (another copy OR a real physical edge)
gets a true local short-or-long. No shadow-sort assumption. -/
theorem copy_local_piece_of_shadow_two_vertices
    (hLocal : D.LocalPieceSystemBound 2)
    (i : I) (a : I ⊕ E)
    (hne : Sum.inl i ≠ a)
    (x y : V) (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i)
    (hiy : y ∈ D.copyCarrier i)
    (hax : x ∈ D.carrier a)
    (hay : y ∈ D.carrier a) :
    D.ShortPiece (Sum.inl i) (Sum.inl x) (Sum.inl y) ∨
    D.LongPiece (Sum.inl i) (Sum.inl x) (Sum.inl y) := by
  cases a with
  | inl j =>
      have hij : i ≠ j := by
        intro hij
        exact hne (by simp [hij])
      exact (D.twoVertexTwoCopyCycle_both_local_pieces
        hLocal i j x y hij hxy
        hix hiy hax hay).1
  | inr e =>
      exact D.copy_piece_of_incident_edge
        hLocal i e x y hxy hix hiy hax hay

/-- A mixed vertex/wagon probe with ANY other distinct lower
label yields an honest physical bridge in chosen witness copy i.
In particular the other label may be a physical CORE A-edge. -/
theorem copy_mixed_bridge_of_shadow_label
    (hBound : D.Bound)
    (i : I) (a : I ⊕ E)
    (hne : Sum.inl i ≠ a)
    (x : V) (p : P)
    (hix : x ∈ D.copyCarrier i)
    (hip : D.Meets (Sum.inl i) p)
    (hax : x ∈ D.carrier a)
    (hap : D.Meets a p) :
    D.Bridge (Sum.inl i) x p :=
  (D.both_bridges hBound (Sum.inl i) a x p hne
    hix hax hip hap).1

end StructuralRamsey.Girth.OrderOneData
