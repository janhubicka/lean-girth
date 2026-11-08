import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# At length two, two wagon boundaries exclude every physical edge label

A literal physical edge belongs to one wagon parent. If it occurs in
a two-occurrence BigCycle whose two distinct boundary connectors are
BOTH wagons, its own incidence would place the same edge in two
distinct parents, which is impossible.

Thus both source labels in such a cycle are genuinely designated.
This is independent of Acceptable, linearity and FullSystemGirthGT,
and does not assert a supreme plan. It sharpens the residual source
length-two classification needed by the actual attached-output
two-owner-cut transfer. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An actual edge label incident with a wagon has exactly that
wagon as its own physical parent. -/
theorem incident_edge_wagon_parent
    (b : E) (p : P)
    (h : D.Incident (Sum.inr b) (Sum.inr p)) :
    D.parent b = p := by
  change D.Meets (Sum.inr b) p at h
  rcases h with ⟨c, hc, hp⟩
  have hcb : c = b := hc
  subst c
  exact hp

/-- With two DISTINCT wagon connectors in a literal BigCycle 2,
both source labels MUST be designated copies, not physical edges.
No system-girth or acceptability hypothesis is required. -/
theorem BigCycle.two_wagon_connectors_all_designated
    (K : D.BigCycle 2) (p q : P)
    (hp : K.connector (0 : Fin 2) = Sum.inr p)
    (hq : K.connector (1 : Fin 2) = Sum.inr q) :
    ∀ j : Fin 2, D.designated (K.label j) := by
  have hpq : p ≠ q := by
    intro heq
    have hSame :
        K.connector (0 : Fin 2) = K.connector (1 : Fin 2) := by
      calc
        K.connector (0 : Fin 2) = Sum.inr p := hp
        _ = Sum.inr q := by rw [heq]
        _ = K.connector (1 : Fin 2) := hq.symm
    exact (by decide : (0 : Fin 2) ≠ 1) (K.connector_injective hSame)
  intro j
  cases hLabel : K.label j with
  | inl i =>
      rw [hLabel]
      trivial
  | inr b =>
      exfalso
      fin_cases j
      · have hLeft : D.Incident (Sum.inr b) (Sum.inr p) := by
          simpa only [hLabel, hp] using K.left_incident (0 : Fin 2)
        have hRight : D.Incident (Sum.inr b) (Sum.inr q) := by
          simpa [hLabel, hq, cyclicSucc] using
            K.right_incident (1 : Fin 2)
        have hParentP := D.incident_edge_wagon_parent b p hLeft
        have hParentQ := D.incident_edge_wagon_parent b q hRight
        exact hpq (hParentP.symm.trans hParentQ)
      · have hLeft : D.Incident (Sum.inr b) (Sum.inr q) := by
          simpa only [hLabel, hq] using K.left_incident (1 : Fin 2)
        have hRight : D.Incident (Sum.inr b) (Sum.inr p) := by
          simpa [hLabel, hp, cyclicSucc] using
            K.right_incident (0 : Fin 2)
        have hParentP := D.incident_edge_wagon_parent b p hRight
        have hParentQ := D.incident_edge_wagon_parent b q hLeft
        exact hpq (hParentP.symm.trans hParentQ)

end StructuralRamsey.Girth.OrderOneData
