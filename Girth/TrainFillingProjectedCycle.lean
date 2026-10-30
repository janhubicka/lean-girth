import Girth.TrainFillingRetainedEdgeContacts
import Girth.TrainFillingRetainedRestriction

/-!
# Actual filling projection with at least three retained connectors

Canonical survivor positions determine the labels and both incidences.
A contracted block uses its unique joining old edge, which need not be
either incident filled edge's cover. The retained-contact theorem proves
physical label separation; original legality proves designated separation.
No projected labels, incidence, adjacency or legal output are premises.
The two-survivor branch is a separate obligation.
-/
namespace StructuralRamsey.Girth.TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

theorem retainedIndex_surjective {n : ℕ} (C : (H).BigCycle n)
    (i : Fin n) (hi : ¬ F.ContractibleBlock copyCarrier copyEdges parent C i) :
    ∃ j, F.retainedIndex copyCarrier copyEdges parent C j = i := by
  classical
  have hmem := (F.retainedPositions_mem_iff copyCarrier copyEdges parent C i).mpr hi
  rw [← F.retainedIndex_image copyCarrier copyEdges parent C] at hmem
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  exact ⟨j, hj⟩

/-- The retained predecessor skips zero or one deleted positions. -/
theorem retainedIndex_predecessor {n : ℕ} (C : (H).BigCycle n)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) :
    let pos := F.retainedIndex copyCarrier copyEdges parent C
    (¬ F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred (pos j)) ∧
      pos (trainCyclicPred j) = trainCyclicPred (pos j)) ∨
    (F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred (pos j)) ∧
      pos (trainCyclicPred j) = trainCyclicPred (trainCyclicPred (pos j))) := by
  classical
  let pos := F.retainedIndex copyCarrier copyEdges parent C
  have hm := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
  by_cases hi : F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred (pos j))
  · right
    refine ⟨hi, ?_⟩
    have hbefore := (F.contractible_neighbours_retained copyCarrier copyEdges parent C _ hi).1
    obtain ⟨a, ha⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C _ hbefore
    have hRight : pos j = cyclicSucc (trainCyclicPred (pos j)) :=
      (cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two (pos j)).symm
    have hab : a ≠ j := by
      intro h
      obtain ⟨_p, _x, _y, _hp, _hx, _hy, hne, _⟩ := hi
      apply hne
      exact ha.symm.trans ((congrArg pos h).trans hRight)
    have hDeleted : ∀ b, pos b ≠ trainCyclicPred (pos j) := by
      intro b hb
      have hkeep := F.retainedIndex_not_contractible copyCarrier copyEdges parent C b
      rw [hb] at hkeep
      exact hkeep hi
    have hj := CyclicRestriction.successor_across_deleted_position
      pos a j (trainCyclicPred (pos j)) hab hDeleted ha hRight
    have hpred := congrArg trainCyclicPred hj
    rw [trainCyclicPred_cyclicSucc_of_two_le hm] at hpred
    rw [hpred]
    exact ha
  · left
    refine ⟨hi, ?_⟩
    obtain ⟨a, ha⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C _ hi
    have hp := CyclicRestriction.predecessor_of_source_predecessor
      hm C.length_ge_two pos j a ha
    rw [← hp]
    exact ha

theorem contractingEdge_exists {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
    ∃ f : F.OldEdge,
      (O).Incident (.inr f) (C.connector (trainCyclicPred i)) ∧
      (O).Incident (.inr f) (C.connector (cyclicSucc i)) ∧
      C.connector i = Sum.inr (parent f) := by
  obtain ⟨p, x, y, f, hp, hx, hy, _hxy, hxf, hyf, hparent, _⟩ :=
    F.contractible_unique_old_edge copyCarrier copyEdges parent C hOld i hi
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hx]; exact hxf
  · rw [hy]; exact hyf
  · rw [hparent]; exact hp

noncomputable def contractingEdge {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) : F.OldEdge :=
  Classical.choose (F.contractingEdge_exists copyCarrier copyEdges parent C hOld i hi)

theorem contractingEdge_spec {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (i : Fin n)
    (hi : F.ContractibleBlock copyCarrier copyEdges parent C i) :
    let f := F.contractingEdge copyCarrier copyEdges parent C hOld i hi
    (O).Incident (.inr f) (C.connector (trainCyclicPred i)) ∧
      (O).Incident (.inr f) (C.connector (cyclicSucc i)) ∧
      C.connector i = Sum.inr (parent f) :=
  Classical.choose_spec (F.contractingEdge_exists copyCarrier copyEdges parent C hOld i hi)

noncomputable def projectedLabel {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) : I ⊕ F.OldEdge := by
  classical
  let i := F.retainedIndex copyCarrier copyEdges parent C j
  exact if hi : F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred i)
    then Sum.inr (F.contractingEdge copyCarrier copyEdges parent C hOld _ hi)
    else F.projectLabel (C.label i)

theorem projectedLabel_right_incident {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) :
    (O).Incident (F.projectedLabel copyCarrier copyEdges parent C hOld j)
      (C.connector (F.retainedIndex copyCarrier copyEdges parent C j)) := by
  classical
  unfold projectedLabel
  split_ifs with hi
  · have h := (F.contractingEdge_spec copyCarrier copyEdges parent C hOld _ hi).2.1
    simpa only [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] using h
  · exact F.projectLabel_incident copyCarrier copyEdges parent _ _ (C.left_incident _)

theorem projectedLabel_left_incident {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) :
    (O).Incident (F.projectedLabel copyCarrier copyEdges parent C hOld j)
      (C.connector (F.retainedIndex copyCarrier copyEdges parent C (trainCyclicPred j))) := by
  classical
  have hpred := F.retainedIndex_predecessor copyCarrier copyEdges parent C j
  rcases hpred with ⟨hkeep, hpos⟩ | ⟨hdelete, hpos⟩
  · rw [hpos]
    simp only [projectedLabel, dif_neg hkeep]
    apply F.projectLabel_incident copyCarrier copyEdges parent
    have h := C.right_incident (trainCyclicPred (F.retainedIndex copyCarrier copyEdges parent C j))
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] at h
    exact h
  · rw [hpos]
    simp only [projectedLabel, dif_pos hdelete]
    exact (F.contractingEdge_spec copyCarrier copyEdges parent C hOld _ hdelete).1

theorem projectedLabel_eq_designated_iff {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hNormal : C.MixedNormalized H)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) (a : I) :
    F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inl a ↔
      C.label (F.retainedIndex copyCarrier copyEdges parent C j) = Sum.inl a := by
  classical
  unfold projectedLabel
  split_ifs with hi
  · obtain ⟨e, f, _he, hf, _hef⟩ :=
      F.contractible_has_edge_occurrences copyCarrier copyEdges parent C hNormal _ hi
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] at hf
    simp only [hf, reduceCtorEq]
  · exact F.projectLabel_eq_designated_iff _ a

theorem projected_designated_predecessor_retained {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) (a : I)
    (ha : F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inl a) :
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C
      (trainCyclicPred (F.retainedIndex copyCarrier copyEdges parent C j)) := by
  classical
  intro hi
  simp only [projectedLabel, dif_pos hi, reduceCtorEq] at ha

theorem projected_adjacent_designated_ne {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hNormal : C.MixedNormalized H)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) (a : I)
    (hj : F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inl a)
    (hs : F.projectedLabel copyCarrier copyEdges parent C hOld (cyclicSucc j) = Sum.inl a) : False := by
  let pos := F.retainedIndex copyCarrier copyEdges parent C
  have hm := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
  have hkeep := F.projected_designated_predecessor_retained copyCarrier copyEdges parent C hOld _ a hs
  have hprev : pos j = trainCyclicPred (pos (cyclicSucc j)) := by
    rcases F.retainedIndex_predecessor copyCarrier copyEdges parent C (cyclicSucc j) with h | h
    · simpa only [trainCyclicPred_cyclicSucc_of_two_le hm] using h.2
    · exact False.elim (hkeep h.1)
  have hnext : cyclicSucc (pos j) = pos (cyclicSucc j) := by
    rw [hprev, cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two]
  have hjSource := (F.projectedLabel_eq_designated_iff copyCarrier copyEdges parent C hOld hNormal j a).mp hj
  have hsSource := (F.projectedLabel_eq_designated_iff copyCarrier copyEdges parent C hOld hNormal (cyclicSucc j) a).mp hs
  apply C.adjacent_ne (pos j)
  rw [hnext]
  exact hjSource.trans hsSource.symm

/-- The actual projected BigCycle, in the at-least-three-survivor branch. -/
noncomputable def projectedCycleOfThree {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hAccept : C.Acceptable)
    (hNormal : C.MixedNormalized H)
    (hm : 3 ≤ (F.retainedPositions copyCarrier copyEdges parent C).card) :
    (O).BigCycle (F.retainedPositions copyCarrier copyEdges parent C).card where
  length_ge_two := by omega
  label := F.projectedLabel copyCarrier copyEdges parent C hOld
  connector := fun j => C.connector (F.retainedIndex copyCarrier copyEdges parent C j)
  adjacent_ne := by
    intro j hEq
    have hm2 := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
    cases hLabel : F.projectedLabel copyCarrier copyEdges parent C hOld j with
    | inl a =>
        exact F.projected_adjacent_designated_ne copyCarrier copyEdges parent C hOld hNormal
          j a hLabel (hEq.symm.trans hLabel)
    | inr f =>
        apply F.projected_adjacent_edge_ne copyCarrier copyEdges parent C hAccept.2.1 hAccept.2.2
          hm (F.retainedIndex copyCarrier copyEdges parent C)
          (F.retainedIndex_not_contractible copyCarrier copyEdges parent C)
          (F.projectedLabel copyCarrier copyEdges parent C hOld)
          (F.projectedLabel_right_incident copyCarrier copyEdges parent C hOld)
          _ j f hLabel (hEq.symm.trans hLabel)
        intro t
        have h := F.projectedLabel_left_incident copyCarrier copyEdges parent C hOld (cyclicSucc t)
        simpa only [trainCyclicPred_cyclicSucc_of_two_le hm2] using h
  connector_injective := C.connector_injective.comp
    (F.retainedIndex copyCarrier copyEdges parent C).injective
  left_incident := F.projectedLabel_right_incident copyCarrier copyEdges parent C hOld
  right_incident := by
    intro j
    have hm2 := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
    have h := F.projectedLabel_left_incident copyCarrier copyEdges parent C hOld (cyclicSucc j)
    simpa only [trainCyclicPred_cyclicSucc_of_two_le hm2] using h

theorem projectedCycleOfThree_acceptable_and_order {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hAccept : C.Acceptable)
    (hNormal : C.MixedNormalized H)
    (hm : 3 ≤ (F.retainedPositions copyCarrier copyEdges parent C).card) :
    let B := F.projectedCycleOfThree copyCarrier copyEdges parent C hOld hAccept hNormal hm
    B.Acceptable ∧ B.twiceOrder ≤ C.twiceOrder := by
  let B := F.projectedCycleOfThree copyCarrier copyEdges parent C hOld hAccept hNormal hm
  obtain ⟨_hLength, hOrder, hA2, hA3⟩ :=
    F.filling_canonical_restriction_bounds copyCarrier copyEdges parent C B hAccept (fun _ => rfl)
  refine ⟨⟨?_, hA2, hA3⟩, hOrder⟩
  intro hOne
  have hLength := B.length_le_twiceOrder
  omega
end StructuralRamsey.Girth.TrainFilling
