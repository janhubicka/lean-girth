import Girth.TrainBottomForestReducedNoA1
import Mathlib.Tactic

/-!
# The single shared physical edge of an allowed bottom two-label cycle

At bottom equality each wagon has precisely one edge. Two distinct
connectors incident with both labels of a genuine two-occurrence
cycle, together with their allowed forest intersection, force ONE
physical edge owned by BOTH labels and incident with BOTH connectors.
This stronger symmetric short statement is used in the exceptional
two-cut transfer; it is not just an unspecified supreme-copy choice.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A genuine two-occurrence bottom cycle supported on two allowed
members has a single common physical edge through each connector.
No A1, designated-label choice, or full-system-girth bound is assumed. -/
theorem BigCycle.bottom_two_common_short_of_allowed
    (C : D.BigCycle 2) (H : D.BottomForestGeometry)
    (hAllowed : AllowedIntersection
      (D.bottomForestPiece H (C.label 0))
      (D.bottomForestPiece H (C.label 1))) :
    ∃ e : E,
      e ∈ D.edges (C.label 0) ∧
      e ∈ D.edges (C.label 1) ∧
      ∀ k : Fin 2, D.Incident (.inr e) (C.connector k) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hConnectorNe : C.connector 0 ≠ C.connector 1 :=
    fun h => h01 (C.connector_injective h)
  have hLeft0 : D.Incident (C.label 0) (C.connector 0) :=
    C.left_incident 0
  have hRight0 : D.Incident (C.label 0) (C.connector 1) := by
    simpa [cyclicSucc] using C.right_incident 1
  have hLeft1 : D.Incident (C.label 1) (C.connector 0) := by
    simpa [cyclicSucc] using C.right_incident 0
  have hRight1 : D.Incident (C.label 1) (C.connector 1) :=
    C.left_incident 1
  obtain ⟨e, he0, he1, hInc0, hInc1⟩ :=
    H.common_short_edge D hAllowed hConnectorNe
      hLeft0 hRight0 hLeft1 hRight1
  refine ⟨e, he0, he1, ?_⟩
  intro k
  fin_cases k
  · exact hInc0
  · exact hInc1

/-- Finite local forests, rather than a full system-girth bound,
supply the symmetric common short edge as soon as two actual
reduct labels are in the requested forest budget. -/
theorem BigCycle.bottom_two_common_short_of_localForest
    (C : D.BigCycle 2) (H : D.BottomForestGeometry)
    (q : ℕ) (hLocal : LocalForestThrough (D.bottomForestPiece H) q)
    (hq : 2 ≤ q) :
    ∃ e : E,
      e ∈ D.edges (C.label 0) ∧
      e ∈ D.edges (C.label 1) ∧
      ∀ k : Fin 2, D.Incident (.inr e) (C.connector k) := by
  have hForest : C.BottomForest D H :=
    C.bottomForest_of_localForest D H q hLocal hq
  let a : Set.range C.label := ⟨C.label 0, ⟨0, rfl⟩⟩
  let b : Set.range C.label := ⟨C.label 1, ⟨1, rfl⟩⟩
  have hab : a ≠ b := by
    intro h
    have hVal := congrArg Subtype.val h
    exact C.adjacent_ne 0 (by simpa [a, b, cyclicSucc] using hVal)
  exact C.bottom_two_common_short_of_allowed
    D H (hForest.pairwiseAllowed hab)

end StructuralRamsey.Girth.OrderOneData
