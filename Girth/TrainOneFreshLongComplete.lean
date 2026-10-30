import Girth.TrainArbitraryReplacementComplete

/-!
# One fresh physical long insertion: actual legal global word

Given one genuinely valid LongValid piece from a source designated
copy at original occurrence j, with a new wagon absent from ALL old
source connectors, replace exactly j by the physical pair
  (first edge, fresh wagon), (last edge, original connector).
All remaining occurrences are KEPT.

The checked arbitrary-replacement theorem then constructs the literal
expanded BigCycle, proves its acceptability and EXACT numerical order,
and pulls any later indexed supreme occurrence back to the original
source cycle. The globally legal word is constructed, not assumed.

This does not prove that the reduced-witness piece lifts physically
into the attached picture, nor the strict geometric-owner cut decrease
after the increased-length insertion. Those are the remaining Track A
geometry obligations. No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A single long insertion with every other original occurrence kept. -/
def BigCycle.onlyLongPieces
    {n : ℕ} (C : D.BigCycle n) (j : Fin n) (e : E) (w : P) (f : E) :
    Fin n → TrainSupremePiece E P :=
  fun k => if k = j then .long e w f else .keep

/-- Real LongValid incidence supplies every local piece-incidence
premise for the single-insertion word; kept pieces need no checks. -/
theorem BigCycle.onlyLongPieces_incidence
    {n : ℕ} (C : D.BigCycle n)
    (source j : Fin n) (e : E) (w : P) (f : E)
    (hLong : C.LongValid D source j e w f) :
    C.LocalPieceIncidence D (C.onlyLongPieces D j e w f) := by
  intro k
  by_cases hk : k = j
  · subst k
    simp only [BigCycle.onlyLongPieces, if_pos rfl]
    change e ≠ f ∧
      D.Incident (.inr e) (C.connector (trainCyclicPred j)) ∧
      D.parent e = w ∧ D.parent f = w ∧
      D.Incident (.inr f) (C.connector j)
    obtain ⟨x, y, hLeft, hRight, _hE, _hF,
      hNe, hParentE, hParentF, hxE, hyF, _hNoPair⟩ := hLong
    refine ⟨hNe, ?_, hParentE, hParentF, ?_⟩
    · rw [hLeft]
      exact hxE
    · rw [hRight]
      exact hyF
  · simp [BigCycle.onlyLongPieces, hk]

/-- Its A2/A3 geometry follows from the SAME genuine LongValid
piece: both boundary connectors are vertices, both meet the
inserted wagon, and no ambient support edge joins them. -/
theorem BigCycle.onlyLongPieces_A2Geometry
    {n : ℕ} (C : D.BigCycle n)
    (source j : Fin n) (e : E) (w : P) (f : E)
    (hLong : C.LongValid D source j e w f) :
    C.LocalLongA2Geometry D (C.onlyLongPieces D j e w f) := by
  intro k a b p hp
  by_cases hk : k = j
  · subst k
    have hEq : e = a ∧ w = p ∧ f = b := by
      simpa [BigCycle.onlyLongPieces] using hp
    rcases hEq with ⟨rfl, rfl, rfl⟩
    obtain ⟨x, y, hLeft, hRight, _hE, _hF,
      _hNe, hParentE, hParentF, hxE, hyF, hNoPair⟩ := hLong
    exact ⟨x, y, hLeft, hRight,
      ⟨e, hParentE, hxE⟩, ⟨f, hParentF, hyF⟩, hNoPair⟩
  · simp [BigCycle.onlyLongPieces, hk] at hp

/-- Only one original occurrence is long, so its real wagon
freshness immediately supplies the uniform freshness interface
required by the global arbitrary-replacement theorem. -/
theorem BigCycle.onlyLongPieces_fresh
    {n : ℕ} (C : D.BigCycle n)
    (j : Fin n) (e : E) (w : P) (f : E)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr w) :
    ∀ (k : Fin n) (a : E) (p : P) (b : E),
      C.onlyLongPieces D j e w f k = .long a p b →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
  intro k a p b hp t
  by_cases hk : k = j
  · subst k
    have hEq : e = a ∧ w = p ∧ f = b := by
      simpa [BigCycle.onlyLongPieces] using hp
    rcases hEq with ⟨rfl, rfl, rfl⟩
    exact hFresh t
  · simp [BigCycle.onlyLongPieces, hk] at hp

/-- A real fresh LongValid piece at ONE original occurrence gives a
genuine globally legal, acceptable output BigCycle of exact original
twice-order; every later globally supreme designated occurrence
reflects back to the ORIGINAL source.  In particular there is no
hidden PlanProducesBigCycle or source-target identification premise. -/
theorem BigCycle.oneFreshLong_complete_of_three_le
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (source j : Fin n) (e : E) (w : P) (f : E)
    (hLong : C.LongValid D source j e w f)
    (hFresh : ∀ t : Fin n, C.connector t ≠ Sum.inr w) :
    ∃ m : ℕ, ∃ H : D.BigCycle m,
      List.ofFn (fun k : Fin m => (H.label k, H.connector k)) =
        C.resultWord D (C.onlyLongPieces D j e w f) ∧
      H.Acceptable ∧ H.twiceOrder = C.twiceOrder ∧
      (∀ kH : Fin m, H.HasSupremeAt D kH →
        ∃ kC : Fin n, C.label kC = H.label kH ∧
          C.HasSupremeAt D kC) := by
  exact C.arbitrary_replacement_complete_of_three_le
    D hAccept hLinear hn
    (C.onlyLongPieces D j e w f)
    (C.onlyLongPieces_incidence D source j e w f hLong)
    (C.onlyLongPieces_A2Geometry D source j e w f hLong)
    (C.onlyLongPieces_fresh D j e w f hFresh)

end StructuralRamsey.Girth.OrderOneData
