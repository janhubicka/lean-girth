import Girth.TrainTwoCopyLongProbe
import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: physical pair or two-edge wagon probes force a local piece
in the ORIGINAL selected copy

At source length two the appropriate original designated B-copy
need NOT be the labelled copy of the reduced geometric witness.
The source old system-girth bound is about the SELECTED old B-copies,
not arbitrary witness standard labels. To construct a real local
piece in the original B-copy from the lower witness, use OLD
physical probe edges after transporting their core incidences to
the old selected standard.

If x,y are distinct vertices of the original selected copy and
there is either (i) an OLD physical support edge through both, or
(ii) two OLD physical edges through x,y respectively in the same
old wagon, with NO OLD pair edge, then the checked old two-vertex
edge or two-edge-long probe forces a ShortPiece or LongPiece
belonging to the ORIGINAL selected B-copy. The cutoff is q>=2.

For mixed vertex/wagon contacts, the old positive order-one bound
and an old physical edge bridging that vertex and wagon force an
actual selected-copy Bridge and hence a ShortPiece.

These are old-copy LOCAL existence results, not complete output
length-two supremacy. No assertion that the physical old probes
are automatically available in the actual attachment; that
remaining core-to-old reflection is a separate obligation.
No appendix or manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Under genuine OLD source SupremeCycleBound at q>=2, a real
physical pair-edge or no-pair same-wagon two-edge probe yields
a local short-or-long piece in the actual ORIGINAL designated
old B-copy, even when that copy is not a reduced witness label. -/
theorem copy_local_piece_of_pair_or_wagon_probe
    {q : ℕ} (hq : 2 ≤ q)
    (hOld : D.SupremeCycleBound q)
    (i : I) (x y : V)
    (hxy : x ≠ y)
    (hix : x ∈ D.copyCarrier i)
    (hiy : y ∈ D.copyCarrier i)
    (hPhysical :
      D.PairEdge x y ∨
      (¬ D.PairEdge x y ∧
        ∃ (w : P) (e f : E),
          D.parent e = w ∧ D.parent f = w ∧
          x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier f)) :
    D.ShortPiece (Sum.inl i) (Sum.inl x) (Sum.inl y) ∨
    D.LongPiece (Sum.inl i) (Sum.inl x) (Sum.inl y) := by
  have hLocal : D.LocalPieceSystemBound 2 := by
    intro n C hAccept hOrder
    exact D.localPieceSystemBound_of_supremeCycleBound
      q hOld n C hAccept (by omega)
  rcases hPhysical with hPair | ⟨hNoPair, w, e, f, hPE, hPF, hXE, hYF⟩
  · obtain ⟨edge, hex, hey⟩ := hPair
    exact D.copy_piece_of_incident_edge hLocal i edge x y
      hxy hix hiy hex hey
  · have hNe : e ≠ f := by
      intro heq
      subst f
      exact hNoPair ⟨e, hXE, hYF⟩
    exact Or.inr (D.copy_long_piece_of_two_edge_probe
      hLocal i e f w x y hNe hxy hix hiy
      hPE hPF hXE hYF hNoPair)

/-- Under old order-one system bound, a TRUE physical bridge
belonging to any old source edge produces a bridge inside the
ORIGINAL designated old B-copy whenever x is in that copy and
the copy actually meets the same old wagon. -/
theorem copy_mixed_bridge_of_old_physical_probe
    (hBound : D.Bound)
    (i : I) (x : V) (p : P)
    (hx : x ∈ D.copyCarrier i)
    (hMeets : D.Meets (Sum.inl i) p)
    (e : E) (hParent : D.parent e = p)
    (hXE : x ∈ D.edgeCarrier e) :
    D.ShortPiece (Sum.inl i) (Sum.inl x) (Sum.inr p) := by
  obtain ⟨f, hf, hPF, hXF⟩ :=
    D.bridge_of_incident_edge hBound (Sum.inl i) x p
      hx hMeets e hParent hXE
  exact ⟨f, hf, hXF, ⟨f, rfl, hPF⟩⟩


/-- The exact OLD mixed probe used by a length-two original selected
B-copy. One original selected-copy edge t establishes its true
old wagon, while an arbitrary real old edge s in that SAME wagon
through original boundary vertex x probes the old bound. The
result is a bridge belonging to the ORIGINAL selected B-copy,
not to a reduced lower gluing standard. -/
theorem copy_bridge_of_old_shared_wagon_edge
    (hBound : D.Bound)
    (i : I) (x : V)
    (s t : E)
    (hx : x ∈ D.copyCarrier i)
    (ht : t ∈ D.copyEdges i)
    (hsX : x ∈ D.edgeCarrier s)
    (hSame : D.parent s = D.parent t) :
    D.Bridge (Sum.inl i) x (D.parent t) := by
  have hMeets : D.Meets (Sum.inl i) (D.parent t) :=
    ⟨t, ht, rfl⟩
  exact D.bridge_of_incident_edge hBound
    (Sum.inl i) x (D.parent t)
    hx hMeets s hSame hsX

end StructuralRamsey.Girth.OrderOneData
