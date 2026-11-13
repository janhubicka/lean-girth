import Girth.TrainBottomMinimalEdgeSingleton
import Girth.TrainFillingMixedNormalization

/-!
# Bottom normalization and the minimum-cut no-mixed-singleton lemma

The pre-existing simultaneous mixed short-normalization handles
designated occurrences.  The minimum geometric owner argument handles
ambient edge labels with a bottom wagon boundary.  The designated
copy's boundary implication is deliberately stated as the remaining
geometry input; no output girth or unknown witness is assumed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P Std Core : Type v} (D : OrderOneData V E I P)

/-- An isolated segment in a minimum bottom owner assignment cannot have a
wagon boundary, provided any designated instance of that segment's mixed
boundary is a genuine short-normalizable wagon contact. -/
theorem BigCycle.bottom_normalized_minimal_no_isolated_wagon
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (hNormalized : C.MixedNormalized D)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E)
    (owner : Fin n → Std ⊕ Core)
    (hAllowed : ∀ j, C.BottomGeometricAllowed D stdCarrier coreToEdge j (owner j))
    (hMinimal : ∀ other : Fin n → Std ⊕ Core,
      (∀ j, C.BottomGeometricAllowed D stdCarrier coreToEdge j (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hWagonSide : (∃ p : P, C.connector k = Sum.inr p) ∨
      (∃ p : P, C.connector (trainCyclicPred k) = Sum.inr p))
    (hDesignatedBoundary : D.designated (C.label k) →
      C.MixedWagonContact D k) : False := by
  cases hLabel : C.label k with
  | inl i =>
      have hDes : D.designated (C.label k) := by
        rw [hLabel]
        trivial
      exact (hNormalized k hDes) (hDesignatedBoundary hDes)
  | inr e =>
      have hWagon : C.connector k = Sum.inr (D.parent e) ∨
          C.connector (trainCyclicPred k) = Sum.inr (D.parent e) := by
        rcases hWagonSide with ⟨p, hp⟩ | ⟨p, hp⟩
        · have hIncident : D.Incident (.inr e) (.inr p) := by
            have h := C.left_incident k
            rw [hLabel, hp] at h
            exact h
          have hParent := D.parent_eq_of_edge_label_wagon_incidence e p hIncident
          left
          rw [hParent]
          exact hp
        · have hIncident : D.Incident (.inr e) (.inr p) := by
            have h := C.right_incident (trainCyclicPred k)
            rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k,
              hLabel, hp] at h
            exact h
          have hParent := D.parent_eq_of_edge_label_wagon_incidence e p hIncident
          right
          rw [hParent]
          exact hp
      exact C.bottom_minimal_no_isolated_edge_wagon D H
        stdCarrier coreToEdge owner hAllowed hMinimal
        k e hLabel hLeftCut hRightCut hWagon

end StructuralRamsey.Girth.OrderOneData
