import Girth.TrainUniversalTopThreeCycleSupreme
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Universal-top system girth >2: classify all short acceptable cycles

At the universal top all actual physical edges have the same wagon.
A big cycle has injectively labelled connectors. Hence at most
ONE connector can be a wagon.

If twiceOrder<=4, the source has at most four occurrences.
Four occurrences would have to alternate vertex and wagon
connectors, thus contain two different wagon positions: impossible.
For three occurrences the budget excludes an all-vertex word;
so exactly one wagon connector occurs, with vertex connectors
on both sides.

The checked two-occurrence source supremeness lemma, together
with the actual three-occurrence short-only construction, gives
a complete FullSystemGirthGT 2 certificate from linearity,
constant parent, designated-copy support coverage and A-strongness.
No forest or previous-rank witness system girth is assumed here.

Instantiating these physical hypotheses in the genuine selected
F_2 local witness is a separate, much smaller bridge.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- All actual wagon connectors must refer to the SAME index at
the universal top; the proof uses physical edge incidence, not
the cardinality of the ambient wagon-label type. -/
theorem BigCycle.wagon_connector_unique_of_constant_parent
    {n : ℕ} (Z : D.BigCycle n)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    {i j : Fin n} {p q : P}
    (hi : Z.connector i = Sum.inr p)
    (hj : Z.connector j = Sum.inr q) : i = j := by
  have hMeetsI : D.Meets (Z.label i) p := by
    have h := Z.left_incident i
    rw [hi] at h
    exact h
  have hMeetsJ : D.Meets (Z.label j) q := by
    have h := Z.left_incident j
    rw [hj] at h
    exact h
  obtain ⟨e, _he, hep⟩ := hMeetsI
  obtain ⟨f, _hf, hfq⟩ := hMeetsJ
  have hpq : p = q := hep.symm.trans ((hConst e f).trans hfq)
  apply Z.connector_injective
  rw [hi, hj, hpq]

/-- A universal-top cycle of four occurrences has order STRICTLY
greater than two. Otherwise all four transitions must be mixed
and two distinct connector positions must both be wagons. -/
theorem BigCycle.four_top_twiceOrder_gt_four
    (Z : D.BigCycle 4)
    (hConst : ∀ e f : E, D.parent e = D.parent f) :
    4 < Z.twiceOrder := by
  by_contra hNot
  have hBudget : Z.twiceOrder ≤ 4 := by omega
  let k0 := connectorKind (Z.connector (0 : Fin 4))
  let k1 := connectorKind (Z.connector (1 : Fin 4))
  let k2 := connectorKind (Z.connector (2 : Fin 4))
  let k3 := connectorKind (Z.connector (3 : Fin 4))
  let w0 := twiceOccurrenceWeight k0 k1
  let w1 := twiceOccurrenceWeight k1 k2
  let w2 := twiceOccurrenceWeight k2 k3
  let w3 := twiceOccurrenceWeight k3 k0
  have hSum : w0 + w1 + w2 + w3 ≤ 4 := by
    simpa [BigCycle.twiceOrder, Fin.sum_univ_four, cyclicSucc,
      w0, w1, w2, w3, k0, k1, k2, k3] using hBudget
  have h0 : 1 ≤ w0 := twiceOccurrenceWeight_one_le k0 k1
  have h1 : 1 ≤ w1 := twiceOccurrenceWeight_one_le k1 k2
  have h2 : 1 ≤ w2 := twiceOccurrenceWeight_one_le k2 k3
  have h3 : 1 ≤ w3 := twiceOccurrenceWeight_one_le k3 k0
  have hw0 : w0 = 1 := by omega
  have hw1 : w1 = 1 := by omega
  have hw2 : w2 = 1 := by omega
  have hk01 : k0 ≠ k1 := by
    intro hEq
    have hTwo : w0 = 2 := by simp [w0, twiceOccurrenceWeight, hEq]
    omega
  have hk12 : k1 ≠ k2 := by
    intro hEq
    have hTwo : w1 = 2 := by simp [w1, twiceOccurrenceWeight, hEq]
    omega
  have hk23 : k2 ≠ k3 := by
    intro hEq
    have hTwo : w2 = 2 := by simp [w2, twiceOccurrenceWeight, hEq]
    omega
  cases hC0 : Z.connector (0 : Fin 4) with
  | inl x =>
      cases hC1 : Z.connector (1 : Fin 4) with
      | inl y =>
          have hEqual : k0 = k1 := by
            simp [k0, k1, connectorKind, hC0, hC1]
          exact (hk01 hEqual).elim
      | inr p =>
          cases hC2 : Z.connector (2 : Fin 4) with
          | inr q =>
              have hEqual : k1 = k2 := by
                simp [k1, k2, connectorKind, hC1, hC2]
              exact (hk12 hEqual).elim
          | inl y =>
              cases hC3 : Z.connector (3 : Fin 4) with
              | inl z =>
                  have hEqual : k2 = k3 := by
                    simp [k2, k3, connectorKind, hC2, hC3]
                  exact (hk23 hEqual).elim
              | inr q =>
                  have hIndices := Z.wagon_connector_unique_of_constant_parent
                    D hConst hC1 hC3
                  exact ((by decide : (1 : Fin 4) ≠ 3) hIndices).elim
  | inr p =>
      cases hC1 : Z.connector (1 : Fin 4) with
      | inr q =>
          have hEqual : k0 = k1 := by
            simp [k0, k1, connectorKind, hC0, hC1]
          exact (hk01 hEqual).elim
      | inl x =>
          cases hC2 : Z.connector (2 : Fin 4) with
          | inl y =>
              have hEqual : k1 = k2 := by
                simp [k1, k2, connectorKind, hC1, hC2]
              exact (hk12 hEqual).elim
          | inr q =>
              have hIndices := Z.wagon_connector_unique_of_constant_parent
                D hConst hC0 hC2
              exact ((by decide : (0 : Fin 4) ≠ 2) hIndices).elim

/-- A three-occurrence universal-top cycle of order at most two has
exactly one wagon connector and two vertex connectors; the word
can be rotated but its pattern is forced by the genuine order. -/
theorem BigCycle.three_top_connector_pattern
    (Z : D.BigCycle 3)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hOrder : Z.twiceOrder ≤ 4) :
    ∃ (w : Fin 3) (p : P) (x y : V),
      Z.connector w = Sum.inr p ∧
      Z.connector (trainCyclicPred w) = Sum.inl x ∧
      Z.connector (cyclicSucc w) = Sum.inl y := by
  have hWagon : ∃ w : Fin 3, ∃ p : P,
      Z.connector w = Sum.inr p := by
    by_contra hNone
    push_neg at hNone
    have h0 : ∃ x : V, Z.connector (0 : Fin 3) = Sum.inl x := by
      cases h : Z.connector (0 : Fin 3) with
      | inl x => exact ⟨x, h⟩
      | inr p => exact (hNone 0 p h).elim
    have h1 : ∃ x : V, Z.connector (1 : Fin 3) = Sum.inl x := by
      cases h : Z.connector (1 : Fin 3) with
      | inl x => exact ⟨x, h⟩
      | inr p => exact (hNone 1 p h).elim
    have h2 : ∃ x : V, Z.connector (2 : Fin 3) = Sum.inl x := by
      cases h : Z.connector (2 : Fin 3) with
      | inl x => exact ⟨x, h⟩
      | inr p => exact (hNone 2 p h).elim
    obtain ⟨x, hx⟩ := h0
    obtain ⟨y, hy⟩ := h1
    obtain ⟨z, hz⟩ := h2
    have hTotal : Z.twiceOrder = 6 := by
      simp [BigCycle.twiceOrder, Fin.sum_univ_three,
        cyclicSucc, hx, hy, hz, connectorKind,
        twiceOccurrenceWeight]
    omega
  obtain ⟨w, p, hw⟩ := hWagon
  have hPredNe : trainCyclicPred w ≠ w := by
    fin_cases w <;> decide
  have hSuccNe : cyclicSucc w ≠ w := by
    fin_cases w <;> decide
  cases hp : Z.connector (trainCyclicPred w) with
  | inr q =>
      have hEq := Z.wagon_connector_unique_of_constant_parent D hConst hp hw
      exact (hPredNe hEq).elim
  | inl x =>
      cases hs : Z.connector (cyclicSucc w) with
      | inr q =>
          have hEq := Z.wagon_connector_unique_of_constant_parent D hConst hs hw
          exact (hSuccNe hEq).elim
      | inl y =>
          exact ⟨w, p, x, y, hw, hp, hs⟩

/-- The only three-occurrence top cycles in the order-two budget
have the vertex/wagon/vertex pattern and hence an ORIGINAL
designated globally supreme label by the checked simultaneous
short-piece constructor. No lower-witness system-girth premise. -/
theorem BigCycle.three_top_supreme_of_order_two
    (Z : D.BigCycle 3) (hAccept : Z.Acceptable)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (hOrder : Z.twiceOrder ≤ 4) :
    Z.HasSimultaneousSupreme := by
  obtain ⟨w, p, x, y, hw, hx, hy⟩ :=
    Z.three_top_connector_pattern D hConst hOrder
  exact Z.three_top_supreme_of_one_wagon
    D hAccept hConst hCover w p x y hw hx hy

/-- Full original selected-copy system girth >2 at the universal
top follows from physical pretrain linearity, one common parent,
A-supported vertices of the designated copies, and A-strong
reflection of every ambient A-edge that meets a selected copy
in two vertices. This is purely local STRUCTURAL geometry and
does not presume a system-girth bound of the witness. -/
theorem fullSystemGirth_two_of_constant_parent
    (hLinear : D.LinearPretrain)
    (hConst : ∀ e f : E, D.parent e = D.parent f)
    (hCover : ∀ i : I, ∀ x ∈ D.copyCarrier i,
      ∃ e : E, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (hStrong : ∀ i : I, ∀ e : E,
      ¬ (D.edgeCarrier e ∩ D.copyCarrier i).Subsingleton →
        e ∈ D.copyEdges i) :
    D.FullSystemGirthGT 2 := by
  refine ⟨hLinear, ?_⟩
  intro n Z hAccept hOrder
  have hMin := Z.length_ge_two
  have hMax := Z.length_le_twiceOrder
  by_cases h2 : n = 2
  · subst n
    exact Z.two_original_supreme_of_constant_parent
      D hAccept hLinear hConst hCover hStrong
  by_cases h3 : n = 3
  · subst n
    exact Z.three_top_supreme_of_order_two
      D hAccept hConst hCover hOrder
  have h4 : n = 4 := by omega
  subst n
  have hContradiction :=
    Z.four_top_twiceOrder_gt_four D hConst
  exact (by omega : False)

end StructuralRamsey.Girth.OrderOneData
