import Girth.TrainActualCutReductionDichotomy
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: literal two-occurrence incidence and mixed bridge classification

For a genuine length-two BigCycle each original label is incident
with BOTH actual connector positions. This is not an extra
symmetry hypothesis: it follows from the four original structure
fields and cyclicSucc exchanging 0 and 1.

Under real positive FullSystemGirthGT, if those connectors are
one vertex and one wagon, both original labels have genuine
physical bridge edges through that vertex in that wagon. These
bridges can differ between the two labels. They are the precise
input to the verified two-cut variable-short source transfer.
No synthetic labels, appendix or support pruning.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Both actual labels of a genuine BigCycle with TWO occurrences
are incident to each of its two actual connectors. -/
theorem BigCycle.two_every_label_incident_every_connector
    (Z : D.BigCycle 2) (k t : Fin 2) :
    D.Incident (Z.label k) (Z.connector t) := by
  fin_cases k <;> fin_cases t
  · exact Z.left_incident (0 : Fin 2)
  · simpa [cyclicSucc] using Z.right_incident (1 : Fin 2)
  · simpa [cyclicSucc] using Z.right_incident (0 : Fin 2)
  · exact Z.left_incident (1 : Fin 2)

/-- A genuine mixed vertex/wagon two-occurrence witness under
positive FullSystemGirthGT supplies a physical bridge at BOTH
actual labels, not just at an existentially chosen supreme copy. -/
theorem BigCycle.two_mixed_bridges_of_fullSystemGirth
    (Z : D.BigCycle 2) {q : ℕ} (hq : 1 ≤ q)
    (hFull : D.FullSystemGirthGT q)
    (x : V) (p : P)
    (hMixed :
      (Z.connector (0 : Fin 2) = Sum.inl x ∧
       Z.connector (1 : Fin 2) = Sum.inr p) ∨
      (Z.connector (0 : Fin 2) = Sum.inr p ∧
       Z.connector (1 : Fin 2) = Sum.inl x)) :
    ∀ k : Fin 2, D.Bridge (Z.label k) x p := by
  have hIncVertex : ∀ k : Fin 2,
      D.Incident (Z.label k) (Sum.inl x) := by
    intro k
    rcases hMixed with h | h
    · rw [← h.1]
      exact BigCycle.two_every_label_incident_every_connector D Z k 0
    · rw [← h.2]
      exact BigCycle.two_every_label_incident_every_connector D Z k 1
  have hIncWagon : ∀ k : Fin 2,
      D.Incident (Z.label k) (Sum.inr p) := by
    intro k
    rcases hMixed with h | h
    · rw [← h.2]
      exact BigCycle.two_every_label_incident_every_connector D Z k 1
    · rw [← h.1]
      exact BigCycle.two_every_label_incident_every_connector D Z k 0
  have hVertex (k : Fin 2) : x ∈ D.carrier (Z.label k) := hIncVertex k
  have hWagon (k : Fin 2) : D.Meets (Z.label k) p := hIncWagon k
  have hDiff : Z.label (0 : Fin 2) ≠ Z.label (1 : Fin 2) := by
    simpa [cyclicSucc] using Z.adjacent_ne (0 : Fin 2)
  have hBound : D.Bound :=
    D.orderOneBound_of_fullSystemGirth_positive hq hFull
  obtain ⟨hBridge0, hBridge1⟩ :=
    D.both_bridges hBound (Z.label 0) (Z.label 1)
      x p hDiff (hVertex 0) (hVertex 1)
      (hWagon 0) (hWagon 1)
  intro k
  fin_cases k
  · exact hBridge0
  · exact hBridge1

end StructuralRamsey.Girth.OrderOneData
