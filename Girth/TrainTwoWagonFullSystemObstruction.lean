import Girth.TrainBigCycleTwoWagonObstruction
import Girth.TrainSimultaneousSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# A full-system-girth witness excludes ANY two-wagon BigCycle of length two

At two different wagon connectors, no short piece can join the
boundaries: one physical edge has just one parent. A long piece
requires two VERTEX endpoints and so is likewise impossible.

Consequently a literal two-occurrence word with two distinct wagon
connectors has no local supreme copy, irrespective of whether its
labels are designated copies or actual edges. Its numerical order
is two and its A1 condition is automatically vacuous; A2 and A3
hold for every length-two BigCycle. A genuine FullSystemGirthGT q
with q>=2 therefore excludes it outright.

This is a generic source/witness lemma. It does NOT assume full
system-girth for the attached output and does not itself transport
the two source connectors through the geometric cut reduction.
The latter is a separate checked actual picture interface. No
appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A two-occurrence word with both distinct boundary connectors
wagons has no possible local short or long supreme replacement.
No designatedness or acceptability assumption is needed. -/
theorem BigCycle.two_wagon_no_localSupreme
    (Z : D.BigCycle 2) (p q : P)
    (hp : Z.connector (0 : Fin 2) = Sum.inr p)
    (hq : Z.connector (1 : Fin 2) = Sum.inr q) :
    ¬ Z.HasLocalSupreme := by
  have hpq : p ≠ q := by
    intro heq
    have hc : Z.connector (0 : Fin 2) =
        Z.connector (1 : Fin 2) := by
      calc
        Z.connector (0 : Fin 2) = Sum.inr p := hp
        _ = Sum.inr q := by rw [heq]
        _ = Z.connector (1 : Fin 2) := hq.symm
    exact (by decide : (0 : Fin 2) ≠ 1) (Z.connector_injective hc)
  intro hLocal
  obtain ⟨k, _hk, hPiece⟩ := hLocal
  fin_cases k
  · have hne : Z.label (1 : Fin 2) ≠ Z.label (0 : Fin 2) := by
      simpa [cyclicSucc] using (Z.adjacent_ne (0 : Fin 2)).symm
    have h := hPiece (1 : Fin 2) hne
    have hAt : D.ShortPiece (Z.label (0 : Fin 2))
        (Sum.inr p) (Sum.inr q) ∨
        D.LongPiece (Z.label (0 : Fin 2))
          (Sum.inr p) (Sum.inr q) := by
      simpa [trainCyclicPred, hp, hq] using h
    exact hpq (D.piece_two_wagon_forces_eq
      (Z.label (0 : Fin 2)) p q hAt)
  · have hne : Z.label (0 : Fin 2) ≠ Z.label (1 : Fin 2) := by
      simpa [cyclicSucc] using Z.adjacent_ne (0 : Fin 2)
    have h := hPiece (0 : Fin 2) hne
    have hAt : D.ShortPiece (Z.label (1 : Fin 2))
        (Sum.inr q) (Sum.inr p) ∨
        D.LongPiece (Z.label (1 : Fin 2))
          (Sum.inr q) (Sum.inr p) := by
      simpa [trainCyclicPred, hp, hq] using h
    have hqp : q = p := D.piece_two_wagon_forces_eq
      (Z.label (1 : Fin 2)) q p hAt
    exact hpq hqp.symm

/-- Even an edge-only two-wagon word has acceptable order two.
Thus FullSystemGirthGT q, q>=2, excludes it, with no assumption
that its two labels are designated. -/
theorem BigCycle.two_wagon_absurd_of_fullSystemGirth
    {q : ℕ} (hFull : D.FullSystemGirthGT q) (hq : 2 ≤ q)
    (Z : D.BigCycle 2) (p r : P)
    (hp : Z.connector (0 : Fin 2) = Sum.inr p)
    (hr : Z.connector (1 : Fin 2) = Sum.inr r) :
    False := by
  have hFour : Z.twiceOrder = 4 := by
    simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
      connectorKind, twiceOccurrenceWeight, hp, hr]
  have hAccept : Z.Acceptable := by
    refine ⟨?_, D.twoCycle_A2 Z, D.twoCycle_A3 Z⟩
    intro hTwo
    omega
  have hBudget : Z.twiceOrder ≤ 2 * q := by omega
  have hGlobal : Z.HasSimultaneousSupreme :=
    hFull.2 2 Z hAccept hBudget
  exact Z.two_wagon_no_localSupreme D p r hp hr
    (Z.localSupreme_of_simultaneous D hGlobal)

end StructuralRamsey.Girth.OrderOneData
