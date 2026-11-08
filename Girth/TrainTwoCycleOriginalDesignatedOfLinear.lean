import Girth.TrainSimultaneousSupreme
import Girth.TrainPhysicalTwoContactsAdjacent
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: every acceptable physical two-cycle in a linear pretrain has
a genuinely designated original source occurrence

A two-occurrence acceptable BigCycle cannot consist of two genuine
physical A-edge labels:
* with distinct vertex connectors x,y, both distinct edges would
  contain x and y, contradicting actual support-edge linearity;
* with vertex/wagon mixed connectors, its twice-order is two, so
  acceptability A1 forces a designated source label;
* with distinct wagon connectors, either physical edge would have
  two different parent wagons, impossible for a physical A-edge.

Consequently every genuinely acceptable source BigCycle of length
exactly two in an actual linear pretrain already contains an original
DESIGNATED label. This is stronger than the A1 order-one condition
and is the necessary first step toward the final original-length-two
two-cut output-girth case. It is NOT a local/global supremacy proof.

No false identification of geometric owners with original labels,
no support pruning, and no appendix or TeX edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Under real physical edge/wagon linearity, an acceptable
BigCycle of length two has an actual original designated label.
No hypothesis about its geometric owner is used. -/
theorem BigCycle.two_has_designated_of_linear
    (Z : D.BigCycle 2)
    (hAccept : Z.Acceptable)
    (hLinear : D.LinearPretrain) :
    ∃ k : Fin 2, D.designated (Z.label k) := by
  cases ha : Z.label (0 : Fin 2) with
  | inl i =>
      exact ⟨0, by simpa [OrderOneData.designated, ha]⟩
  | inr e =>
      cases hb : Z.label (1 : Fin 2) with
      | inl j =>
          exact ⟨1, by simpa [OrderOneData.designated, hb]⟩
      | inr f =>
          have hne : e ≠ f := by
            intro heq
            have hDiff := Z.adjacent_ne (0 : Fin 2)
            simp [cyclicSucc, ha, hb, heq] at hDiff
          have h0e : D.Incident (Sum.inr e)
              (Z.connector (0 : Fin 2)) := by
            simpa [ha] using Z.left_incident (0 : Fin 2)
          have h1e : D.Incident (Sum.inr e)
              (Z.connector (1 : Fin 2)) := by
            simpa [cyclicSucc, ha] using Z.right_incident (1 : Fin 2)
          have h0f : D.Incident (Sum.inr f)
              (Z.connector (0 : Fin 2)) := by
            simpa [cyclicSucc, hb] using Z.right_incident (0 : Fin 2)
          have h1f : D.Incident (Sum.inr f)
              (Z.connector (1 : Fin 2)) := by
            simpa [hb] using Z.left_incident (1 : Fin 2)
          cases h0 : Z.connector (0 : Fin 2) with
          | inl x =>
              cases h1 : Z.connector (1 : Fin 2) with
              | inl y =>
                  have hxy : x ≠ y := by
                    intro heq
                    have hSame :
                        Z.connector (0 : Fin 2) =
                          Z.connector (1 : Fin 2) := by
                      calc
                        Z.connector 0 = Sum.inl x := h0
                        _ = Sum.inl y := by rw [heq]
                        _ = Z.connector 1 := h1.symm
                    exact (by decide : (0 : Fin 2) ≠ 1)
                      (Z.connector_injective hSame)
                  have hxe : x ∈ D.edgeCarrier e := by
                    simpa [Incident, carrier, h0] using h0e
                  have hyE : y ∈ D.edgeCarrier e := by
                    simpa [Incident, carrier, h1] using h1e
                  have hxf : x ∈ D.edgeCarrier f := by
                    simpa [Incident, carrier, h0] using h0f
                  have hyF : y ∈ D.edgeCarrier f := by
                    simpa [Incident, carrier, h1] using h1f
                  exact False.elim <| hxy <|
                    hLinear.1 e f hne ⟨hxe, hxf⟩ ⟨hyE, hyF⟩
              | inr p =>
                  have hOrder : Z.twiceOrder = 2 := by
                    simp [BigCycle.twiceOrder, Fin.sum_univ_two,
                      cyclicSucc, connectorKind, twiceOccurrenceWeight,
                      h0, h1]
                  obtain ⟨k, hk⟩ := hAccept.1 hOrder
                  fin_cases k
                  · have bad : False := by
                      simpa [OrderOneData.designated, ha] using hk
                    exact bad.elim
                  · have bad : False := by
                      simpa [OrderOneData.designated, hb] using hk
                    exact bad.elim
          | inr p =>
              cases h1 : Z.connector (1 : Fin 2) with
              | inl y =>
                  have hOrder : Z.twiceOrder = 2 := by
                    simp [BigCycle.twiceOrder, Fin.sum_univ_two,
                      cyclicSucc, connectorKind, twiceOccurrenceWeight,
                      h0, h1]
                  obtain ⟨k, hk⟩ := hAccept.1 hOrder
                  fin_cases k
                  · have bad : False := by
                      simpa [OrderOneData.designated, ha] using hk
                    exact bad.elim
                  · have bad : False := by
                      simpa [OrderOneData.designated, hb] using hk
                    exact bad.elim
              | inr q =>
                  have hpq : p ≠ q := by
                    intro heq
                    have hSame :
                        Z.connector (0 : Fin 2) =
                          Z.connector (1 : Fin 2) := by
                      calc
                        Z.connector 0 = Sum.inr p := h0
                        _ = Sum.inr q := by rw [heq]
                        _ = Z.connector 1 := h1.symm
                    exact (by decide : (0 : Fin 2) ≠ 1)
                      (Z.connector_injective hSame)
                  have hep : D.parent e = p := by
                    have hInc : D.Meets (Sum.inr e) p := by
                      simpa only [OrderOneData.Incident, h0] using h0e
                    obtain ⟨a, ha, hp⟩ := hInc
                    have hEq : a = e := ha
                    simpa only [hEq] using hp
                  have heq : D.parent e = q := by
                    have hInc : D.Meets (Sum.inr e) q := by
                      simpa only [OrderOneData.Incident, h1] using h1e
                    obtain ⟨a, ha, hp⟩ := hInc
                    have hEq : a = e := ha
                    simpa only [hEq] using hp
                  exact False.elim (hpq (hep.symm.trans heq))

end StructuralRamsey.Girth.OrderOneData
