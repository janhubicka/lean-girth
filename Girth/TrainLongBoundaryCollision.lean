import Girth.TrainFreshLongWagon

/-!
# Circulation: noncollision at short/long replacement boundaries

An acceptable cycle may be replaced by short and long pieces.  The
nontrivial cyclic-label inequalities occur where consecutive replacement
pieces both begin/end with physical edge labels.

At a fresh wagon, every ambient edge in that wagon which is incident with
an ORIGINAL connector must meet a vertex connector, since no original
connector is this wagon.  Thus a short edge in that wagon through BOTH
boundaries of an occurrence makes that occurrence use the same fresh wagon
as a neighbouring long piece.  The checked A3 uniqueness of a fresh wagon
for an occurrence rules this out.

These elementary lemmas establish the three edge/edge boundary collisions:
short--long, long--short and long--long, directly from actual ShortValid and
LongValid.  The global cyclic word and supreme-plan composition are not
claimed here.  No appendix hypotheses occur.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An edge belonging to a fresh wagon cannot meet an original wagon
connector. Any incidence with the original cycle is a vertex incidence,
and makes that vertex lie in the fresh wagon. -/
theorem BigCycle.incident_edge_in_fresh_wagon_vertex
    {n : ℕ} (C : D.BigCycle n) (p : P)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (e : E) (he : D.parent e = p)
    (t : Fin n) (hInc : D.Incident (.inr e) (C.connector t)) :
    C.InWagonAt p t := by
  cases hCt : C.connector t with
  | inl x =>
      have hx : x ∈ D.edgeCarrier e := by
        have h := hInc
        rw [hCt] at h
        exact h
      exact ⟨x, hCt, e, he, hx⟩
  | inr q =>
      have h := hInc
      rw [hCt] at h
      change D.Meets (.inr e) q at h
      obtain ⟨f, hf, hfp⟩ := h
      have hfe : f = e := by simpa [OrderOneData.edges] using hf
      subst f
      have hqp : q = p := hfp.symm.trans he
      exact False.elim (hFresh t (by rw [hCt, hqp]))

/-- Both original boundary positions of a valid short edge lie in its
own parent wagon, provided that wagon was not an original connector. -/
theorem BigCycle.shortValid_fresh_wagon_boundaries
    {n : ℕ} (C : D.BigCycle n)
    (k j : Fin n) (e : E) (p : P)
    (hShort : C.ShortValid D k j e)
    (he : D.parent e = p)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.InWagonAt p (trainCyclicPred j) ∧ C.InWagonAt p j := by
  exact ⟨C.incident_edge_in_fresh_wagon_vertex D p hFresh e he
      (trainCyclicPred j) hShort.2.1,
    C.incident_edge_in_fresh_wagon_vertex D p hFresh e he j hShort.2.2⟩

/-- Both original boundary positions of a valid long piece lie in the
wagon introduced by that piece. -/
theorem BigCycle.longValid_wagon_boundaries
    {n : ℕ} (C : D.BigCycle n)
    (k j : Fin n) (e f : E) (p : P)
    (hLong : C.LongValid D k j e p f) :
    C.InWagonAt p (trainCyclicPred j) ∧ C.InWagonAt p j := by
  obtain ⟨x, y, hx, hy, _he, _hf, _hne,
    hep, hfp, hxe, hyf, _hNoPair⟩ := hLong
  exact ⟨⟨x, hx, e, hep, hxe⟩, ⟨y, hy, f, hfp, hyf⟩⟩

/-- The original successor of an occurrence is different from the
occurrence in any big cycle, including length two. -/
theorem BigCycle.ne_cyclicSucc
    {n : ℕ} (C : D.BigCycle n) (j : Fin n) :
    j ≠ cyclicSucc j := by
  intro h
  exact C.adjacent_ne j (congrArg C.label h)

/-- A short piece followed by a long piece cannot use the same physical
edge across their common original connector.  Otherwise their shared
fresh wagon sees both boundaries of two different occurrences. -/
theorem BigCycle.short_long_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k i : Fin n) (a b c : E) (p : P)
    (hShort : C.ShortValid D k i a)
    (hLong : C.LongValid D k (cyclicSucc i) b p c)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    a ≠ b := by
  intro hab
  have hbp : D.parent b = p := by
    obtain ⟨_x, _y, _hx, _hy, _hb, _hc, _hne,
      hbp, _hcp, _hxb, _hyc, _⟩ := hLong
    exact hbp
  have hap : D.parent a = p := by rw [hab]; exact hbp
  have hShortB := C.shortValid_fresh_wagon_boundaries
    D k i a p hShort hap hFresh
  have hLongB := C.longValid_wagon_boundaries
    D k (cyclicSucc i) b c p hLong
  have hEq := C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p hFresh i (cyclicSucc i)
    hShortB.1 hShortB.2 hLongB.1 hLongB.2
  exact C.ne_cyclicSucc D i hEq

/-- A long piece followed by a short piece has distinct physical
edge labels at their common original connector. -/
theorem BigCycle.long_short_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k i : Fin n) (a b c : E) (p : P)
    (hLong : C.LongValid D k i a p b)
    (hShort : C.ShortValid D k (cyclicSucc i) c)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    b ≠ c := by
  intro hbc
  have hbp : D.parent b = p := by
    obtain ⟨_x, _y, _hx, _hy, _ha, _hb, _hne,
      _hap, hbp, _hxa, _hyb, _⟩ := hLong
    exact hbp
  have hcp : D.parent c = p := by rw [← hbc]; exact hbp
  have hLongB := C.longValid_wagon_boundaries D k i a b p hLong
  have hShortB := C.shortValid_fresh_wagon_boundaries
    D k (cyclicSucc i) c p hShort hcp hFresh
  have hEq := C.nonconnector_wagon_boundary_occurrence_unique
    D hAccept hn p hFresh i (cyclicSucc i)
    hLongB.1 hLongB.2 hShortB.1 hShortB.2
  exact C.ne_cyclicSucc D i hEq

/-- Two neighbouring long pieces cannot end and begin with the same
physical edge, as that would identify their fresh parent wagons. -/
theorem BigCycle.long_long_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k i : Fin n) (a b c d : E) (p q : P)
    (hLongI : C.LongValid D k i a p b)
    (hLongJ : C.LongValid D k (cyclicSucc i) c q d)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    b ≠ c := by
  intro hbc
  have hbp : D.parent b = p := by
    obtain ⟨_x, _y, _hx, _hy, _ha, _hb, _hne,
      _hap, hbp, _hxa, _hyb, _⟩ := hLongI
    exact hbp
  have hcq : D.parent c = q := by
    obtain ⟨_x, _y, _hx, _hy, _hc, _hd, _hne,
      hcq, _hdq, _hxc, _hyd, _⟩ := hLongJ
    exact hcq
  have hpq : p = q := by
    calc
      p = D.parent b := hbp.symm
      _ = D.parent c := congrArg D.parent hbc
      _ = q := hcq
  subst q
  exact C.longPieces_fresh_wagon_distinct D hAccept hn p hFresh
    i (cyclicSucc i) (C.ne_cyclicSucc D i) k k
    a b c d hLongI hLongJ

end StructuralRamsey.Girth.OrderOneData
