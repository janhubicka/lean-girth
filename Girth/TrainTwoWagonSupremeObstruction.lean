import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: two distinct wagon boundaries forbid a two-occurrence supreme plan

For a genuine two-occurrence BigCycle whose BOTH connectors are
distinct wagons, neither label can be simultaneously supreme:
* a short physical A-edge has exactly one wagon parent, so it
  cannot meet two different wagon connectors;
* a long replacement requires two vertex boundary connectors.

The adjacent-label inequality ensures that at least the OTHER
occurrence must be replaced. This is an obstruction to a legal
local piece, and therefore even to a globally valid simultaneous
replacement. We retain the full two-label and two-wagon identity.

At cutoff >=2, a FullSystemGirthGT witness thus excludes any
ACCEPTABLE two-occurrence two-wagon BigCycle, since its twice-order
is exactly four. This is useful for the exactly-two-owner-cut
witness reduction, and leaves two-vertex and mixed connector cases.

No assertion that such a reduced word is automatically acceptable,
no source-level replacement, no appendix, and no manuscript changes.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- One physical edge belongs to exactly one parent wagon; a short
piece between distinct wagon connectors would require two parents. -/
theorem not_shortPiece_between_distinct_wagons
    (a : I ⊕ E) (p q : P) (hpq : p ≠ q) :
    ¬ D.ShortPiece a (Sum.inr p) (Sum.inr q) := by
  rintro ⟨e, _he, hEP, hEQ⟩
  have hP : D.parent e = p := by
    simpa [Incident, Meets, edges] using hEP
  have hQ : D.parent e = q := by
    simpa [Incident, Meets, edges] using hEQ
  exact hpq (hP.symm.trans hQ)

/-- A long piece always has two vertex boundaries. -/
theorem not_longPiece_between_wagons
    (a : I ⊕ E) (p q : P) :
    ¬ D.LongPiece a (Sum.inr p) (Sum.inr q) := by
  rintro ⟨x, y, w, e, f, hx, _⟩
  cases hx

/-- At two occurrences with distinct wagon connectors neither
possible designated target label can be locally supreme. -/
theorem BigCycle.no_localSupreme_of_two_wagon_connectors
    (Z : D.BigCycle 2)
    (p q : P)
    (h0 : Z.connector 0 = Sum.inr p)
    (h1 : Z.connector 1 = Sum.inr q) :
    ¬ Z.HasLocalSupreme := by
  have hpq : p ≠ q := by
    intro hpq
    have hidx : (0 : Fin 2) = 1 := Z.connector_injective (by
      calc
        Z.connector 0 = Sum.inr p := h0
        _ = Sum.inr q := by rw [hpq]
        _ = Z.connector 1 := h1.symm)
    exact (by decide : (0 : Fin 2) ≠ 1) hidx
  have hLabels : Z.label (0 : Fin 2) ≠ Z.label 1 := by
    simpa [cyclicSucc] using Z.adjacent_ne (0 : Fin 2)
  rintro ⟨k, _hk, hPieces⟩
  fin_cases k
  · have hPiece := hPieces (1 : Fin 2) hLabels.symm
    have hPhysical :
        D.ShortPiece (Z.label 0) (Sum.inr p) (Sum.inr q) ∨
        D.LongPiece (Z.label 0) (Sum.inr p) (Sum.inr q) := by
      simpa [trainCyclicPred, h0, h1] using hPiece
    rcases hPhysical with hs | hl
    · exact D.not_shortPiece_between_distinct_wagons
        (Z.label 0) p q hpq hs
    · exact D.not_longPiece_between_wagons
        (Z.label 0) p q hl
  · have hPiece := hPieces (0 : Fin 2) hLabels
    have hPhysical :
        D.ShortPiece (Z.label 1) (Sum.inr q) (Sum.inr p) ∨
        D.LongPiece (Z.label 1) (Sum.inr q) (Sum.inr p) := by
      simpa [trainCyclicPred, h0, h1] using hPiece
    rcases hPhysical with hs | hl
    · exact D.not_shortPiece_between_distinct_wagons
        (Z.label 1) q p hpq.symm hs
    · exact D.not_longPiece_between_wagons
        (Z.label 1) q p hl

/-- The obstruction applies a fortiori to the ACTUAL globally legal
simultaneous replacement, not just to the weaker local-piece condition. -/
theorem BigCycle.no_simultaneousSupreme_of_two_wagon_connectors
    (Z : D.BigCycle 2)
    (p q : P)
    (h0 : Z.connector 0 = Sum.inr p)
    (h1 : Z.connector 1 = Sum.inr q) :
    ¬ Z.HasSimultaneousSupreme := by
  intro hSupreme
  exact D.BigCycle.no_localSupreme_of_two_wagon_connectors
    Z p q h0 h1
    (D.BigCycle.localSupreme_of_simultaneous Z hSupreme)

/-- Both wagon connectors contribute weight two at each of the
two occurrences. -/
theorem BigCycle.twiceOrder_eq_four_of_two_wagon_connectors
    (Z : D.BigCycle 2)
    (p q : P)
    (h0 : Z.connector 0 = Sum.inr p)
    (h1 : Z.connector 1 = Sum.inr q) :
    Z.twiceOrder = 4 := by
  simp [BigCycle.twiceOrder, Fin.sum_univ_two,
    cyclicSucc, connectorKind, h0, h1, twiceOccurrenceWeight]

/-- At any cutoff at least two, FullSystemGirthGT excludes every
ACCEPTABLE two-occurrence two-wagon cycle. This does not claim
automatic acceptability of an arbitrary witness reduct. -/
theorem BigCycle.no_acceptable_two_wagon_of_fullSystemGirth
    {qcut : ℕ} (hqcut : 2 ≤ qcut)
    (hFull : D.FullSystemGirthGT qcut)
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (p q : P)
    (h0 : Z.connector 0 = Sum.inr p)
    (h1 : Z.connector 1 = Sum.inr q) :
    False := by
  have hOrder : Z.twiceOrder = 4 :=
    D.BigCycle.twiceOrder_eq_four_of_two_wagon_connectors
      Z p q h0 h1
  have hBounded : Z.twiceOrder ≤ 2 * qcut := by
    rw [hOrder]
    omega
  exact D.BigCycle.no_simultaneousSupreme_of_two_wagon_connectors
    Z p q h0 h1 (hFull.2 2 Z hAccept hBounded)

end StructuralRamsey.Girth.OrderOneData
