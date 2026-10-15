import Girth.TrainFreshWagonA2
import Girth.TrainLongBoundaryCollision

/-!
# Circulation: retained physical edges and adjacent replacement pieces

The broad admissible-replacement lemma permits keeping an ORIGINAL physical
edge label; it is not restricted to simultaneous supreme plans, whose kept
labels are designated. The checked supreme-plan boundary theorem alone does
not cover this case.

A retained edge is incident at BOTH original boundaries of its occurrence.
If it equals a neighbouring short replacement edge, the same physical edge
meets THREE distinct original connector positions, impossible by A2/A3.
If it equals the first or last edge of a neighbouring long replacement,
its fresh wagon contains the two original boundaries of TWO distinct
occurrences, impossible by checked A3 occurrence uniqueness.

These lemmas close the retained-edge/short and retained-edge/long cases
without assuming a supreme plan, a legal replacement word, or output
wagon linearity. General arbitrary-plan assembly remains separate.
No appendix statement is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A kept original physical edge has both original occurrence incidences,
including the preceding connector. -/
theorem BigCycle.retainedEdge_both_incident
    {n : ℕ} (C : D.BigCycle n) (i : Fin n) (e : E)
    (hLabel : C.label i = Sum.inr e) :
    D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
      D.Incident (.inr e) (C.connector i) := by
  have hPrev := C.right_incident (trainCyclicPred i)
  rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i,
    hLabel] at hPrev
  have hHere := C.left_incident i
  rw [hLabel] at hHere
  exact ⟨hPrev, hHere⟩

/-- If the retained edge is in a fresh wagon, that wagon contains both
original boundary positions of the retained occurrence. -/
theorem BigCycle.retainedEdge_fresh_wagon_boundaries
    {n : ℕ} (C : D.BigCycle n) (i : Fin n) (e : E) (p : P)
    (hLabel : C.label i = Sum.inr e)
    (he : D.parent e = p)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.InWagonAt p (trainCyclicPred i) ∧ C.InWagonAt p i := by
  have hInc := C.retainedEdge_both_incident D i e hLabel
  exact ⟨C.incident_edge_in_fresh_wagon_vertex D p hFresh e he
      (trainCyclicPred i) hInc.1,
    C.incident_edge_in_fresh_wagon_vertex D p hFresh e he i hInc.2⟩

/-- An original retained edge cannot equal the short edge chosen for the
NEXT occurrence (no assumption that the short edge comes from one
designated supreme label). -/
theorem BigCycle.retained_short_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i k : Fin n) (a b : E)
    (hLabel : C.label i = Sum.inr a)
    (hShort : C.ShortValid D k (cyclicSucc i) b) :
    a ≠ b := by
  intro hab
  subst b
  have hInc := C.retainedEdge_both_incident D i a hLabel
  have hSuccSelf : i ≠ cyclicSucc i := C.ne_cyclicSucc D i
  have hPredSelf : trainCyclicPred i ≠ i := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
    rw [h] at hs
    exact hSuccSelf hs.symm
  exact C.not_edge_incident_three_distinct D hAccept a
    (trainCyclicPred i) i (cyclicSucc i)
    hPredSelf (trainCyclicPred_ne_cyclicSucc_of_three_le hn i)
    hSuccSelf hInc.1 hInc.2 hShort.2.2

/-- A short replacement followed by an original retained physical edge
likewise cannot repeat that edge label. -/
theorem BigCycle.short_retained_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i k : Fin n) (a b : E)
    (hShort : C.ShortValid D k i a)
    (hLabel : C.label (cyclicSucc i) = Sum.inr b) :
    a ≠ b := by
  intro hab
  subst b
  have hInc := C.retainedEdge_both_incident D (cyclicSucc i) a hLabel
  have hSuccSelf : i ≠ cyclicSucc i := C.ne_cyclicSucc D i
  have hPredSelf : trainCyclicPred i ≠ i := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
    rw [h] at hs
    exact hSuccSelf hs.symm
  exact C.not_edge_incident_three_distinct D hAccept a
    (trainCyclicPred i) i (cyclicSucc i)
    hPredSelf (trainCyclicPred_ne_cyclicSucc_of_three_le hn i)
    hSuccSelf hShort.2.1 hShort.2.2 hInc.2

/-- An original retained edge cannot coincide with the FIRST edge of a
neighbouring long piece: one fresh wagon would then carry both original
boundary pairs of different occurrences. -/
theorem BigCycle.retained_long_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i k : Fin n) (a b c : E) (p : P)
    (hLabel : C.label i = Sum.inr a)
    (hLong : C.LongValid D k (cyclicSucc i) b p c)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    a ≠ b := by
  intro hab
  have hbp : D.parent b = p := by
    obtain ⟨_x, _y, _hx, _hy, _hb, _hc, _hne,
      hbp, _hcp, _hxb, _hyc, _⟩ := hLong
    exact hbp
  have hap : D.parent a = p := by rw [hab]; exact hbp
  have hRet := C.retainedEdge_fresh_wagon_boundaries
    D i a p hLabel hap hFresh
  have hLongB := C.longValid_wagon_boundaries
    D k (cyclicSucc i) b c p hLong
  have heq := C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p hFresh i (cyclicSucc i)
    hRet.1 hRet.2 hLongB.1 hLongB.2
  exact C.ne_cyclicSucc D i heq

/-- A long piece followed by a retained physical edge cannot repeat
the long piece's LAST edge. -/
theorem BigCycle.long_retained_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (i k : Fin n) (a b c : E) (p : P)
    (hLong : C.LongValid D k i a p b)
    (hLabel : C.label (cyclicSucc i) = Sum.inr c)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    b ≠ c := by
  intro hbc
  have hbp : D.parent b = p := by
    obtain ⟨_x, _y, _hx, _hy, _ha, _hb, _hne,
      _hap, hbp, _hxa, _hyb, _⟩ := hLong
    exact hbp
  have hcp : D.parent c = p := by rw [← hbc]; exact hbp
  have hLongB := C.longValid_wagon_boundaries D k i a b p hLong
  have hRet := C.retainedEdge_fresh_wagon_boundaries D
    (cyclicSucc i) c p hLabel hcp hFresh
  have heq := C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p hFresh i (cyclicSucc i)
    hLongB.1 hLongB.2 hRet.1 hRet.2
  exact C.ne_cyclicSucc D i heq

end StructuralRamsey.Girth.OrderOneData
