import Girth.TrainCyclicOwnerIsolatedNonincrease
import Girth.TrainBottomWagonNeighbourEdge

/-!
# A minimum bottom geometric assignment has no isolated edge at a wagon

Owners are Standard ⊕ Core; a core owner labels a true physical edge,
while a standard owner is defined by carrier containment. If an
isolated edge occurrence has a wagon boundary, its adjacent occurrence
must be standard-owned and contains the same physical edge. Reassigning
to that standard decreases the cut count. This is the complete ambient
edge-label half of the no-mixed-singleton argument. The designated-label
half still requires short normalization and boundary geometry.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P Std Core : Type v} (D : OrderOneData V E I P)

/-- Actual geometric ownership has two disjoint sorts; core owners map to
physical edges, while standards may geometrically contain foreign labels. -/
def BigCycle.BottomGeometricAllowed {n : ℕ} (C : D.BigCycle n)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E) (k : Fin n) :
    Std ⊕ Core → Prop
  | .inl s => D.carrier (C.label k) ⊆ stdCarrier s
  | .inr b => C.label k = Sum.inr (coreToEdge b)

/-- If an ambient edge is followed by its bottom wagon connector, the next
owner is a standard containing the entire physical edge, not a core edge. -/
theorem BigCycle.bottom_next_standard_of_edge_wagon
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E)
    (owner : Fin n → Std ⊕ Core)
    (hAllowed : ∀ k, C.BottomGeometricAllowed D stdCarrier coreToEdge k (owner k))
    (k : Fin n) (e : E)
    (hLabel : C.label k = Sum.inr e)
    (hWagon : C.connector k = Sum.inr (D.parent e)) :
    ∃ s : Std, owner (cyclicSucc k) = Sum.inl s ∧
      D.edgeCarrier e ⊆ stdCarrier s := by
  have hNextEdge : D.edgeCarrier e ⊆ D.carrier (C.label (cyclicSucc k)) :=
    C.next_carrier_contains_bottom_wagon_edge D H k e hWagon
  have hNextMeet : D.Meets (C.label (cyclicSucc k)) (D.parent e) := by
    have h := C.right_incident k
    rw [hWagon] at h
    exact h
  cases hNextOwner : owner (cyclicSucc k) with
  | inl s =>
      have hContain := hAllowed (cyclicSucc k)
      rw [hNextOwner] at hContain
      change D.carrier (C.label (cyclicSucc k)) ⊆ stdCarrier s at hContain
      exact ⟨s, hNextOwner, hNextEdge.trans hContain⟩
  | inr b =>
      have hNextLabel := hAllowed (cyclicSucc k)
      rw [hNextOwner] at hNextLabel
      change C.label (cyclicSucc k) = Sum.inr (coreToEdge b) at hNextLabel
      rw [hNextLabel] at hNextMeet
      obtain ⟨f, hf, hParent⟩ := hNextMeet
      have hEq : f = coreToEdge b := hf
      subst f
      have hEdgeEq : coreToEdge b = e := H.parent_injective hParent
      have hBoth : C.label k = C.label (cyclicSucc k) := by
        rw [hLabel, hNextLabel, hEdgeEq]
      exact False.elim (C.adjacent_ne k hBoth)

/-- The corresponding previous-label assertion uses the genuine cyclic
predecessor, including the last-to-first position. -/
theorem BigCycle.bottom_previous_standard_of_edge_wagon
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E)
    (owner : Fin n → Std ⊕ Core)
    (hAllowed : ∀ k, C.BottomGeometricAllowed D stdCarrier coreToEdge k (owner k))
    (k : Fin n) (e : E)
    (hLabel : C.label k = Sum.inr e)
    (hWagon : C.connector (trainCyclicPred k) = Sum.inr (D.parent e)) :
    ∃ s : Std, owner (trainCyclicPred k) = Sum.inl s ∧
      D.edgeCarrier e ⊆ stdCarrier s := by
  let p := trainCyclicPred k
  have hPrevEdge : D.edgeCarrier e ⊆ D.carrier (C.label p) :=
    C.previous_carrier_contains_bottom_wagon_edge D H k e hWagon
  have hPrevMeet : D.Meets (C.label p) (D.parent e) := by
    have h := C.left_incident p
    rw [hWagon] at h
    exact h
  cases hPrevOwner : owner p with
  | inl s =>
      have hContain := hAllowed p
      rw [hPrevOwner] at hContain
      change D.carrier (C.label p) ⊆ stdCarrier s at hContain
      exact ⟨s, hPrevOwner, hPrevEdge.trans hContain⟩
  | inr b =>
      have hPrevLabel := hAllowed p
      rw [hPrevOwner] at hPrevLabel
      change C.label p = Sum.inr (coreToEdge b) at hPrevLabel
      rw [hPrevLabel] at hPrevMeet
      obtain ⟨f, hf, hParent⟩ := hPrevMeet
      have hEq : f = coreToEdge b := hf
      subst f
      have hEdgeEq : coreToEdge b = e := H.parent_injective hParent
      have hBoth : C.label p = C.label k := by
        rw [hPrevLabel, hLabel, hEdgeEq]
      have hDifferent := C.adjacent_ne p
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k] at hDifferent
      exact False.elim (hDifferent hBoth)

/-- No isolated ambient EDGE label in a minimal geometric owner assignment
can have a wagon connector on either side. Both owner sorts are covered. -/
theorem BigCycle.bottom_minimal_no_isolated_edge_wagon
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E)
    (owner : Fin n → Std ⊕ Core)
    (hAllowed : ∀ k, C.BottomGeometricAllowed D stdCarrier coreToEdge k (owner k))
    (hMinimal : ∀ other : Fin n → Std ⊕ Core,
      (∀ k, C.BottomGeometricAllowed D stdCarrier coreToEdge k (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n) (e : E)
    (hLabel : C.label k = Sum.inr e)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hWagon : C.connector k = Sum.inr (D.parent e) ∨
      C.connector (trainCyclicPred k) = Sum.inr (D.parent e)) : False := by
  have hNeighbour : ∃ s : Std,
      C.BottomGeometricAllowed D stdCarrier coreToEdge k (Sum.inl s) ∧
      ((Sum.inl s : Std ⊕ Core) = owner (trainCyclicPred k) ∨
       (Sum.inl s : Std ⊕ Core) = owner (cyclicSucc k)) := by
    rcases hWagon with hNext | hPrev
    · obtain ⟨s, hs, hSub⟩ := C.bottom_next_standard_of_edge_wagon
        D H stdCarrier coreToEdge owner hAllowed k e hLabel hNext
      refine ⟨s, ?_, Or.inr hs.symm⟩
      change D.carrier (C.label k) ⊆ stdCarrier s
      simpa only [hLabel, D.carrier] using hSub
    · obtain ⟨s, hs, hSub⟩ := C.bottom_previous_standard_of_edge_wagon
        D H stdCarrier coreToEdge owner hAllowed k e hLabel hPrev
      refine ⟨s, ?_, Or.inl hs.symm⟩
      change D.carrier (C.label k) ⊆ stdCarrier s
      simpa only [hLabel, D.carrier] using hSub
  obtain ⟨s, hCan, hAdj⟩ := hNeighbour
  classical
  let alternative : Fin n → Std ⊕ Core :=
    cyclicReplaceOwner owner k (Sum.inl s)
  have hAltAllowed : ∀ j,
      C.BottomGeometricAllowed D stdCarrier coreToEdge j (alternative j) := by
    intro j
    by_cases hj : j = k
    · subst j
      have hChoice : alternative k = Sum.inl s := by
        simp [alternative, cyclicReplaceOwner]
      rw [hChoice]
      exact hCan
    · have hSame : alternative j = owner j := by
        simp [alternative, cyclicReplaceOwner, hj]
      rw [hSame]
      exact hAllowed j
  have hAdjacent : owner (cyclicSucc k) = Sum.inl s ∨
      owner (trainCyclicPred k) = Sum.inl s := by
    rcases hAdj with hp | hs
    · exact Or.inr hp.symm
    · exact Or.inl hs.symm
  have hStrict := cyclicOwnerChanges_replace_isolated_strict_of_neighbor
    C.length_ge_two owner k (Sum.inl s) hLeftCut hRightCut hAdjacent
  exact (not_lt_of_ge (hMinimal alternative hAltAllowed)) hStrict

end StructuralRamsey.Girth.OrderOneData
