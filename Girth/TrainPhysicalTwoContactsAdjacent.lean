import Girth.TrainShortReplacementNeighbour
import Mathlib.Tactic

/-!
# Path A: every physical short bridge has adjacent source connector endpoints

An actual edge in an acceptable BigCycle cannot meet two distinct
nonadjacent connector positions. This uses no chosen supreme target
and no additional linearity assumption:

* wagon/wagon: an edge has one parent and source connectors are injective;
* wagon/vertex: source A2 confines the vertex to the adjacent positions;
* vertex/vertex: if the edge's wagon is old, the edge would meet THREE
  distinct connector positions, forbidden by the checked A2/A3
  three-contact lemma; if it is fresh, source A3 confines its two
  vertex contacts to a single adjacent pair.

This is the missing physical obstruction to lifting reduced ShortValid
pieces over source owner runs of length greater than one.
No appendix, no manuscript validation marker.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If one physical edge is incident with a wagon connector p,
then its literal parent wagon is p. -/
theorem edge_wagon_incidence_parent_eq
    (e : E) (p : P)
    (h : D.Incident (.inr e) (.inr p)) :
    D.parent e = p := by
  change D.Meets (.inr e) p at h
  obtain ⟨f, hf, hp⟩ := h
  have hfe : f = e := by
    simpa [OrderOneData.edges] using hf
  subst f
  exact hp

/-- An actual physical edge meeting two distinct source connector
positions can only join cyclically neighbouring positions. This
includes vertex/vertex, vertex/wagon, wagon/vertex and wagon/wagon
cases, with the original last-to-first wrap included.

Importantly, this is not merely the exclusion of THREE contacts:
source A2/A3 also exclude the exceptional two nonadjacent contacts. -/
theorem BigCycle.physical_edge_two_contacts_adjacent
    {n : ℕ} (K : D.BigCycle n) (hAccept : K.Acceptable)
    (e : E) (a b : Fin n) (hab : a ≠ b)
    (ha : D.Incident (.inr e) (K.connector a))
    (hb : D.Incident (.inr e) (K.connector b)) :
    b = cyclicSucc a ∨ a = cyclicSucc b := by
  cases hCa : K.connector a with
  | inl x =>
      have hAx : x ∈ D.edgeCarrier e := by
        simpa [OrderOneData.Incident, OrderOneData.carrier, hCa] using ha
      cases hCb : K.connector b with
      | inl y =>
          have hBy : y ∈ D.edgeCarrier e := by
            simpa [OrderOneData.Incident, OrderOneData.carrier, hCb] using hb
          let w : P := D.parent e
          have hWa : K.InWagonAt w a :=
            ⟨x, hCa, ⟨e, rfl, hAx⟩⟩
          have hWb : K.InWagonAt w b :=
            ⟨y, hCb, ⟨e, rfl, hBy⟩⟩
          by_cases hOld : ∃ t : Fin n, K.connector t = Sum.inr w
          · obtain ⟨t, ht⟩ := hOld
            have hat : a ≠ t := by
              intro hEq
              have hh := congrArg K.connector hEq
              rw [hCa, ht] at hh
              cases hh
            have hbt : b ≠ t := by
              intro hEq
              have hh := congrArg K.connector hEq
              rw [hCb, ht] at hh
              cases hh
            have hAtT : D.Incident (.inr e) (K.connector t) := by
              rw [ht]
              change D.Meets (.inr e) (D.parent e)
              exact ⟨e, rfl, rfl⟩
            exact False.elim
              (K.not_edge_incident_three_distinct D hAccept
                e a b t hab hat hbt ha hb hAtT)
          · have hFresh : ∀ t : Fin n,
                K.connector t ≠ Sum.inr w := by
              intro t ht
              exact hOld ⟨t, ht⟩
            obtain ⟨root, hWindow⟩ := hAccept.2.2 w hFresh
            rcases hWindow a hWa with hAroot | hAnext
            · rcases hWindow b hWb with hBroot | hBnext
              · exact False.elim (hab (hAroot.trans hBroot.symm))
              · left
                rw [hAroot, hBnext]
            · rcases hWindow b hWb with hBroot | hBnext
              · right
                rw [hAnext, hBroot]
              · exact False.elim (hab (hAnext.trans hBnext.symm))
      | inr p =>
          have hAtP : D.Incident (.inr e) (.inr p) := by
            simpa only [hCb] using hb
          have hParent : D.parent e = p :=
            D.edge_wagon_incidence_parent_eq e p hAtP
          have hWa : K.InWagonAt p a :=
            ⟨x, hCa, ⟨e, hParent, hAx⟩⟩
          rcases hAccept.2.1.1 b p hCb a hWa with hPred | hNext
          · left
            rw [hPred]
            exact (cyclicSucc_trainCyclicPred_of_two_le
              K.length_ge_two b).symm
          · right
            exact hNext
  | inr p =>
      have hAtP : D.Incident (.inr e) (.inr p) := by
        simpa only [hCa] using ha
      have hParent : D.parent e = p :=
        D.edge_wagon_incidence_parent_eq e p hAtP
      cases hCb : K.connector b with
      | inl y =>
          have hBy : y ∈ D.edgeCarrier e := by
            simpa [OrderOneData.Incident, OrderOneData.carrier, hCb] using hb
          have hWb : K.InWagonAt p b :=
            ⟨y, hCb, ⟨e, hParent, hBy⟩⟩
          rcases hAccept.2.1.1 a p hCa b hWb with hPred | hNext
          · right
            rw [hPred]
            exact (cyclicSucc_trainCyclicPred_of_two_le
              K.length_ge_two a).symm
          · left
            exact hNext
      | inr q =>
          have hAtQ : D.Incident (.inr e) (.inr q) := by
            simpa only [hCb] using hb
          have hParentQ : D.parent e = q :=
            D.edge_wagon_incidence_parent_eq e q hAtQ
          have hpq : p = q := hParent.symm.trans hParentQ
          have hSame : K.connector a = K.connector b := by
            rw [hCa, hCb, hpq]
          exact False.elim (hab (K.connector_injective hSame))

end StructuralRamsey.Girth.OrderOneData
