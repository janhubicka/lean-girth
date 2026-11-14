import Girth.TrainBottomMinimalEdgeSingleton
import Girth.TrainFillingMixedNormalization
import Girth.ForestDistinctBoundaryAllowed

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


/-- A complete small-or-whole core boundary containing a genuine bottom
edge must equal that edge. The core may have other unrelated edges;
linearity and two distinct vertices of the given edge suffice. -/
theorem BottomForestGeometry.vertex_mem_shared_edge_of_complete_boundary
    (H : D.BottomForestGeometry)
    (a : I ⊕ E) (S : Set V) (K : Set (Set V))
    (hBoundary : SmallOrWholeEdgeBoundary K S (D.bottomForestPiece H a))
    (e : E) (he : e ∈ D.edges a)
    (heS : D.edgeCarrier e ⊆ S)
    (x : V) (hxa : x ∈ D.carrier a) (hxs : x ∈ S) :
    x ∈ D.edgeCarrier e := by
  have hEdgeSub : D.edgeCarrier e ⊆ D.carrier a ∩ S := by
    intro z hz
    exact ⟨H.edge_subset a e he hz, heS hz⟩
  rcases hBoundary with hSmall | ⟨f, _hfK, hfPiece, hInter⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := H.edge_nontrivial e
    exact False.elim (huv (hSmall (hEdgeSub hu) (hEdgeSub hv)))
  · change f ∈ D.edgeCarrier '' D.edges a at hfPiece
    obtain ⟨b, hb, rfl⟩ := hfPiece
    have hSub : D.edgeCarrier e ⊆ D.edgeCarrier b := by
      intro z hz
      rw [← hInter]
      exact hEdgeSub hz
    have heb : e = b := H.edge_eq_of_subset D hSub
    subst b
    rw [← hInter]
    exact ⟨hxa, hxs⟩

/-- At a designated mixed bottom occurrence whose vertex is in the
core, a complete core boundary forces a genuine ambient short piece.
Both cyclic orientations are treated with their literal incidences. -/
theorem BigCycle.mixedWagonContact_of_complete_core_boundary
    {n : ℕ} (C : D.BigCycle n)
    (H : D.BottomForestGeometry)
    (S : Set V) (K : Set (Set V))
    (hBoundary :
      ∀ a : I ⊕ E, D.designated a →
        SmallOrWholeEdgeBoundary K S (D.bottomForestPiece H a))
    (k : Fin n) (hDesignated : D.designated (C.label k))
    (x : V) (p : P)
    (hMixed :
      (C.connector (trainCyclicPred k) = Sum.inl x ∧
        C.connector k = Sum.inr p) ∨
      (C.connector (trainCyclicPred k) = Sum.inr p ∧
        C.connector k = Sum.inl x))
    (hxCore : x ∈ S)
    (hWagonCore : ∀ e : E, D.parent e = p → D.edgeCarrier e ⊆ S) :
    C.MixedWagonContact D k := by
  have hxLabel : x ∈ D.carrier (C.label k) := by
    rcases hMixed with ⟨hPrev, _hHere⟩ | ⟨_hPrev, hHere⟩
    · have h := C.right_incident (trainCyclicPred k)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k,
        hPrev] at h
      exact h
    · have h := C.left_incident k
      rw [hHere] at h
      exact h
  have hMeets : D.Meets (C.label k) p := by
    rcases hMixed with ⟨_hPrev, hHere⟩ | ⟨hPrev, _hHere⟩
    · have h := C.left_incident k
      rw [hHere] at h
      exact h
    · have h := C.right_incident (trainCyclicPred k)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k,
        hPrev] at h
      exact h
  obtain ⟨e, he, hp⟩ := hMeets
  have hxe : x ∈ D.edgeCarrier e :=
    H.vertex_mem_shared_edge_of_complete_boundary D
      (C.label k) S K (hBoundary (C.label k) hDesignated)
      e he (hWagonCore e hp) x hxLabel hxCore
  exact ⟨x, p, ⟨e, hp, hxe⟩, hMixed⟩

/-- The no-mixed-singleton conclusion of the bottom argument.
The remaining physical input states that both mixed cut connectors are
in the *actual* common core, with the wagon's complete edge inside
that core. No extra supreme-copy assumption appears. -/
theorem BigCycle.bottom_normalized_minimal_no_mixed_singleton_of_boundary
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (hNormalized : C.MixedNormalized D)
    (stdCarrier : Std → Set V) (coreToEdge : Core → E)
    (owner : Fin n → Std ⊕ Core)
    (hAllowed : ∀ j, C.BottomGeometricAllowed D stdCarrier coreToEdge j (owner j))
    (hMinimal : ∀ other : Fin n → Std ⊕ Core,
      (∀ j, C.BottomGeometricAllowed D stdCarrier coreToEdge j (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (S : Set V) (K : Set (Set V))
    (hBoundary :
      ∀ a : I ⊕ E, D.designated a →
        SmallOrWholeEdgeBoundary K S (D.bottomForestPiece H a))
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hCoreMixed :
      ∃ x : V, ∃ p : P,
        ((C.connector (trainCyclicPred k) = Sum.inl x ∧
          C.connector k = Sum.inr p) ∨
         (C.connector (trainCyclicPred k) = Sum.inr p ∧
          C.connector k = Sum.inl x)) ∧
        x ∈ S ∧
        (∀ e : E, D.parent e = p → D.edgeCarrier e ⊆ S)) : False := by
  obtain ⟨x, p, hMixed, hxCore, hWagonCore⟩ := hCoreMixed
  apply C.bottom_normalized_minimal_no_isolated_wagon D H
    hNormalized stdCarrier coreToEdge owner hAllowed hMinimal
    k hLeftCut hRightCut
  · rcases hMixed with ⟨_hp, hHere⟩ | ⟨hPrev, _hq⟩
    · exact Or.inl ⟨p, hHere⟩
    · exact Or.inr ⟨p, hPrev⟩
  · intro hDesignated
    exact C.mixedWagonContact_of_complete_core_boundary D H S K
      hBoundary k hDesignated x p hMixed hxCore hWagonCore

end StructuralRamsey.Girth.OrderOneData
