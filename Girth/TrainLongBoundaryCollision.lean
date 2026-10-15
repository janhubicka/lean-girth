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


/-- Adjacent short pieces cannot choose the same edge at length ≥3:
that edge would meet three different original connector positions. -/
theorem BigCycle.short_short_boundary_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k i : Fin n) (e f : E)
    (hShortI : C.ShortValid D k i e)
    (hShortJ : C.ShortValid D k (cyclicSucc i) f) :
    e ≠ f := by
  intro hef
  subst f
  have hSucc : i ≠ cyclicSucc i := C.ne_cyclicSucc D i
  have hPred : trainCyclicPred i ≠ i := by
    intro h
    have hs := cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i
    rw [h] at hs
    exact hSucc hs.symm
  exact C.not_edge_incident_three_distinct D hAccept e
    (trainCyclicPred i) i (cyclicSucc i)
    hPred (trainCyclicPred_ne_cyclicSucc_of_three_le hn i) hSucc
    hShortI.2.1 hShortI.2.2 hShortJ.2.2

/-- The local long-piece data of a chosen replacement plan. -/
theorem BigCycle.longValid_of_piece_eq_long
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (e f : E) (p : P)
    (hPiece : pieces j = .long e p f) :
    C.LongValid D k j e p f := by
  have hne : C.label j ≠ C.label k := by
    intro heq
    have h := (hPlan j).1 heq
    rw [hPiece] at h
    cases h
  have h := (hPlan j).2 hne
  simpa [hPiece] using h

/-- First and last physical/designated labels of one replacement piece,
before any global indexing or cyclic-word construction. -/
def BigCycle.pieceFirstLabel (a : I ⊕ E) :
    TrainSupremePiece E P → I ⊕ E
  | .keep => a
  | .short e => .inr e
  | .long e _ _ => .inr e

def BigCycle.pieceLastLabel (a : I ⊕ E) :
    TrainSupremePiece E P → I ⊕ E
  | .keep => a
  | .short e => .inr e
  | .long _ _ f => .inr f

/-- Global ADJACENT-LABEL inequality for any simultaneous replacement plan
whose long-piece wagons are fresh. This combines the four physical-edge
collisions with the disjointness of designated and edge labels.  It is
independent of the difficult finite indexing for the complete output word. -/
theorem BigCycle.plan_adjacent_piece_labels_ne
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∀ i : Fin n,
      C.pieceLastLabel D (C.label i) (pieces i) ≠
      C.pieceFirstLabel D (C.label (cyclicSucc i))
        (pieces (cyclicSucc i)) := by
  intro i
  cases hi : pieces i with
  | keep =>
      have hI : C.label i = C.label k :=
        C.label_eq_supreme_of_keep D k i pieces hPlan hi
      cases hj : pieces (cyclicSucc i) with
      | keep =>
          have hJ : C.label (cyclicSucc i) = C.label k :=
            C.label_eq_supreme_of_keep D k (cyclicSucc i) pieces hPlan hj
          exact False.elim (C.adjacent_ne i (hI.trans hJ.symm))
      | short f =>
          have hNe := D.designated_ne_actualEdge (C.label k) f hk
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj, hI]
            using hNe
      | long e p f =>
          have hNe := D.designated_ne_actualEdge (C.label k) e hk
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj, hI]
            using hNe
  | short e =>
      have hShortI : C.ShortValid D k i e :=
        C.shortValid_of_piece_eq_short D k i pieces hPlan e hi
      cases hj : pieces (cyclicSucc i) with
      | keep =>
          have hJ : C.label (cyclicSucc i) = C.label k :=
            C.label_eq_supreme_of_keep D k (cyclicSucc i) pieces hPlan hj
          have hNe := (D.designated_ne_actualEdge (C.label k) e hk).symm
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj, hJ]
            using hNe
      | short f =>
          have hShortJ : C.ShortValid D k (cyclicSucc i) f :=
            C.shortValid_of_piece_eq_short D k (cyclicSucc i) pieces hPlan f hj
          have hNe := C.short_short_boundary_ne D hAccept hn k i e f
            hShortI hShortJ
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj]
            using hNe
      | long f p g =>
          have hLongJ : C.LongValid D k (cyclicSucc i) f p g :=
            C.longValid_of_piece_eq_long D k (cyclicSucc i) pieces hPlan
              f g p hj
          have hNe := C.short_long_boundary_ne D hAccept hn k i e f g p
            hShortI hLongJ (hFresh (cyclicSucc i) f p g hj)
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj]
            using hNe
  | long e p f =>
      have hLongI : C.LongValid D k i e p f :=
        C.longValid_of_piece_eq_long D k i pieces hPlan e f p hi
      have hFreshI := hFresh i e p f hi
      cases hj : pieces (cyclicSucc i) with
      | keep =>
          have hJ : C.label (cyclicSucc i) = C.label k :=
            C.label_eq_supreme_of_keep D k (cyclicSucc i) pieces hPlan hj
          have hNe := (D.designated_ne_actualEdge (C.label k) f hk).symm
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj, hJ]
            using hNe
      | short g =>
          have hShortJ : C.ShortValid D k (cyclicSucc i) g :=
            C.shortValid_of_piece_eq_short D k (cyclicSucc i) pieces hPlan g hj
          have hNe := C.long_short_boundary_ne D hAccept hn k i e f g p
            hLongI hShortJ hFreshI
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj]
            using hNe
      | long g q h =>
          have hLongJ : C.LongValid D k (cyclicSucc i) g q h :=
            C.longValid_of_piece_eq_long D k (cyclicSucc i) pieces hPlan
              g h q hj
          have hNe := C.long_long_boundary_ne D hAccept hn k i
            e f g h p q hLongI hLongJ hFreshI
          simpa [BigCycle.pieceLastLabel, BigCycle.pieceFirstLabel, hi, hj]
            using hNe

end StructuralRamsey.Girth.OrderOneData
