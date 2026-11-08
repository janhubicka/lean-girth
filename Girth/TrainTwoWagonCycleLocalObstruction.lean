import Girth.TrainBigCycleTwoWagonObstruction
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: no genuine two-occurrence wagon/wagon cycle under local girth two

The already checked no-two-designated-meet-two-wagons theorem
rules out two designated labels. In fact it rules out EVERY
physical BigCycle of length two whose two distinct connectors
are wagons: an ordinary physical A-edge label has just one
parent wagon, so it cannot meet both connectors. Consequently
both source labels must be designated, and then the checked
two-designated obstruction applies.

This does not assume linearity or impose an artificial original
selected-copy label; it is a generic OrderOneData fact.
No appendix or manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- One physical edge has exactly one parent wagon. -/
private theorem edge_label_two_wagon_forces_eq
    (e : E) (p q : P)
    (hp : D.Incident (Sum.inr e) (Sum.inr p))
    (hq : D.Incident (Sum.inr e) (Sum.inr q)) :
    p = q := by
  change D.Meets (Sum.inr e) p at hp
  change D.Meets (Sum.inr e) q at hq
  obtain ⟨a, ha, hap⟩ := hp
  obtain ⟨b, hb, hbq⟩ := hq
  have hae : a = e := ha
  have hbe : b = e := hb
  have hpe : D.parent e = p := by
    simpa only [hae] using hap
  have hqe : D.parent e = q := by
    simpa only [hbe] using hbq
  exact hpe.symm.trans hqe

/-- An actual two-cycle with two distinct wagon connectors is
excluded by the order-two local-piece-system girth condition.
This handles physical and designated original label sorts. -/
theorem BigCycle.two_wagon_impossible_of_localPieceSystemBound_two
    (hLocal : D.LocalPieceSystemBound 2)
    (Z : D.BigCycle 2)
    (p q : P)
    (h0 : Z.connector (0 : Fin 2) = Sum.inr p)
    (h1 : Z.connector (1 : Fin 2) = Sum.inr q) : False := by
  have hpq : p ≠ q := by
    intro heq
    have hConn : Z.connector (0 : Fin 2) = Z.connector (1 : Fin 2) := by
      calc
        Z.connector 0 = Sum.inr p := h0
        _ = Sum.inr q := by rw [heq]
        _ = Z.connector 1 := h1.symm
    exact (by decide : (0 : Fin 2) ≠ 1) (Z.connector_injective hConn)
  cases ha : Z.label (0 : Fin 2) with
  | inr e =>
      have hep : D.Incident (Sum.inr e) (Sum.inr p) := by
        simpa [ha, h0] using Z.left_incident (0 : Fin 2)
      have heq : D.Incident (Sum.inr e) (Sum.inr q) := by
        simpa [cyclicSucc, ha, h1] using Z.right_incident (1 : Fin 2)
      exact hpq (D.edge_label_two_wagon_forces_eq e p q hep heq)
  | inl i =>
      cases hb : Z.label (1 : Fin 2) with
      | inr e =>
          have hep : D.Incident (Sum.inr e) (Sum.inr p) := by
            simpa [cyclicSucc, hb, h0] using Z.right_incident (0 : Fin 2)
          have heq : D.Incident (Sum.inr e) (Sum.inr q) := by
            simpa [hb, h1] using Z.left_incident (1 : Fin 2)
          exact hpq (D.edge_label_two_wagon_forces_eq e p q hep heq)
      | inl j =>
          have hij : i ≠ j := by
            intro heq
            have hd := Z.adjacent_ne (0 : Fin 2)
            simp [cyclicSucc, ha, hb, heq] at hd
          have hip : D.Meets (Sum.inl i) p := by
            have h := Z.left_incident (0 : Fin 2)
            simpa only [OrderOneData.Incident, ha, h0] using h
          have hiq : D.Meets (Sum.inl i) q := by
            have h := Z.right_incident (1 : Fin 2)
            simpa [OrderOneData.Incident, cyclicSucc, ha, h1] using h
          have hjp : D.Meets (Sum.inl j) p := by
            have h := Z.right_incident (0 : Fin 2)
            simpa [OrderOneData.Incident, cyclicSucc, hb, h0] using h
          have hjq : D.Meets (Sum.inl j) q := by
            have h := Z.left_incident (1 : Fin 2)
            simpa only [OrderOneData.Incident, hb, h1] using h
          exact D.no_two_designated_meet_two_wagons
            hLocal i j p q hij hpq hip hiq hjp hjq

end StructuralRamsey.Girth.OrderOneData
