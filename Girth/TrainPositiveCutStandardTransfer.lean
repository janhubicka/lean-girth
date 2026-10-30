import Girth.TrainArbitraryReplacementComplete

/-!
# Positive-cut transfer: an actual standard-local supreme copy pulls back

This module factors the positive-cut argument at the point where an arbitrary
physical replacement has already been constructed. The selected standard is
not assumed to be an original designated B-label. The missing *geometric*
step is isolated in the predicates hInside and hBound below.

In particular, the conclusion is supremeness of the ORIGINAL source
cycle, and the old bound is used only on the replacement cycle.
No final recursion or output-wagon linearity is claimed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Once a geometrically legal arbitrary replacement lies in a chosen
standard, a supreme designated occurrence found in that standard
pulls back to the original source cycle. The target of the replacement
need not already occur as a designated source label.

The predicate `InStandard` records the actual physical containment
condition to be established by the later selected-picture geometry.
The hypothesis `hOldBound` is deliberately only a bound for
acceptable replacement cycles IN that standard. -/
theorem BigCycle.supreme_of_arbitrary_replacement_in_standard_of_three_le
    {n q : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (hOrder : C.twiceOrder ≤ 2 * q)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (InStandard : ∀ {m : ℕ}, D.BigCycle m → Prop)
    (hInside : ∀ (m : ℕ) (B : D.BigCycle m),
      List.ofFn (fun j : Fin m => (B.label j, B.connector j)) =
        C.resultWord D pieces → InStandard B)
    (hOldBound : ∀ (m : ℕ) (B : D.BigCycle m),
      InStandard B → B.Acceptable →
      B.twiceOrder ≤ 2 * q → B.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  obtain ⟨m, B, hWord, hBAccept, hSameOrder, hPullback⟩ :=
    C.arbitrary_replacement_complete_of_three_le
      D hAccept hLinear hn pieces hInc hGeom hFresh
  have hInStandard : InStandard B := hInside m B hWord
  have hBOrder : B.twiceOrder ≤ 2 * q := by
    rw [hSameOrder]
    exact hOrder
  obtain ⟨kB, hkDesignated, hBPlan⟩ :=
    hOldBound m B hInStandard hBAccept hBOrder
  obtain ⟨kC, _, hCSupreme⟩ :=
    hPullback kB ⟨hkDesignated, hBPlan⟩
  exact C.hasSimultaneousSupreme_of_hasSupremeAt D kC hCSupreme

/-- The boundary interface, valid also for length-two/order-one source
cycles, once a literal output BigCycle and designated retention are provided.
Unlike the length-at-least-three theorem, legality is not automatic here.
The designated retention premise is exactly what A1 needs at order one. -/
theorem BigCycle.supreme_of_legal_replacement_in_standard
    {n m q : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hOrder : C.twiceOrder ≤ 2 * q)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (hRetain : C.twiceOrder = 2 →
      ∃ j : Fin m, D.designated (B.label j))
    (InStandard : D.BigCycle m → Prop)
    (hInside : InStandard B)
    (hOldBound : ∀ K : D.BigCycle m,
      InStandard K → K.Acceptable →
      K.twiceOrder ≤ 2 * q → K.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  obtain ⟨hBAccept, hSameOrder, hPullback⟩ :=
    C.arbitrary_legal_replacement_all_conclusions
      D B hAccept hLinear pieces hGeom hWord hRetain
  have hBOrder : B.twiceOrder ≤ 2 * q := by
    rw [hSameOrder]
    exact hOrder
  obtain ⟨kB, hkDesignated, hBPlan⟩ :=
    hOldBound B hInside hBAccept hBOrder
  obtain ⟨kC, _, hCSupreme⟩ :=
    hPullback kB ⟨hkDesignated, hBPlan⟩
  exact C.hasSimultaneousSupreme_of_hasSupremeAt D kC hCSupreme

end StructuralRamsey.Girth.OrderOneData
