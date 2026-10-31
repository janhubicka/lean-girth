import Girth.TrainFillingProjectedCycle
import Girth.TrainEdgeOnlyConstantParent

/-!
# Actual filling projection at every source and retained length

Equal edge labels in a two-survivor reduct would lift to physical source
edges with one constant parent. The existing edge-only obstruction rules
this out. This is the longer-source/two-survivor case as well as length two.
The same parent transfer proves A1 without assuming exact order equality.
No legal target cycle, output girth, or designated occurrence is a premise.
-/
namespace StructuralRamsey.Girth

private theorem fin_eq_or_succ_of_two {n : ℕ} (hn : n = 2) (i j : Fin n) :
    i = j ∨ i = cyclicSucc j := by
  subst n
  fin_cases i <;> fin_cases j <;> simp [cyclicSucc]

namespace OrderOneData
universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

private theorem parent_of_edge_wagon_incidence (e : E) (p : P)
    (h : D.Incident (.inr e) (.inr p)) : D.parent e = p := by
  obtain ⟨f, hf, hp⟩ := h
  have hfe : f = e := hf
  subst f
  exact hp

/-- A literal edge-only cycle of order one has constant parent, without
any acceptability or linearity assumption. -/
theorem BigCycle.orderOne_edge_only_constant_parent {n : ℕ} (C : D.BigCycle n)
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (hOrder : C.twiceOrder = 2) : ∃ p : P, ∀ i, D.parent (edge i) = p := by
  have hn : n = 2 := by
    have := C.length_le_twiceOrder
    have := C.length_ge_two
    omega
  subst n
  have hWagon : ∃ (k : Fin 2) (p : P), C.connector k = Sum.inr p := by
    cases h0 : C.connector 0 with
    | inl x =>
        cases h1 : C.connector 1 with
        | inl y =>
            have hFour : C.twiceOrder = 4 := by
              simp [BigCycle.twiceOrder, Fin.sum_univ_two, cyclicSucc,
                h0, h1, connectorKind, twiceOccurrenceWeight]
            omega
        | inr p => exact ⟨1, p, h1⟩
    | inr p => exact ⟨0, p, h0⟩
  obtain ⟨k, p, hp⟩ := hWagon
  refine ⟨p, ?_⟩
  intro i
  apply parent_of_edge_wagon_incidence D (edge i) p
  rcases fin_eq_or_succ_of_two rfl i k with hi | hi
  · subst i
    simpa only [hLabel k, hp] using C.left_incident k
  · rw [hi]
    simpa only [hLabel (cyclicSucc k), hp] using C.right_incident k
end OrderOneData

namespace TrainFilling
universe v
variable {V I P : Type v}
variable (F : TrainFilling V) (copyCarrier : I → Set V)
variable (copyEdges : I → Set F.OldEdge) (parent : F.OldEdge → P)
local notation "O" => F.oldData copyCarrier copyEdges parent
local notation "H" => F.filledData copyCarrier copyEdges parent

/-- A projected physical edge gives the parent of each source occurrence
in its block, not an equality with the covers of those occurrences. -/
theorem projected_edge_source_parents {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hNormal : C.MixedNormalized H)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card)
    (f : F.OldEdge)
    (hLabel : F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inr f) :
    let i := F.retainedIndex copyCarrier copyEdges parent C j
    (∃ e : F.NewEdge, C.label i = Sum.inr e ∧ parent (F.cover e) = parent f) ∧
    (F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred i) →
      ∃ e : F.NewEdge, C.label (trainCyclicPred i) = Sum.inr e ∧
        parent (F.cover e) = parent f) := by
  classical
  let i := F.retainedIndex copyCarrier copyEdges parent C j
  change (∃ e : F.NewEdge, C.label i = Sum.inr e ∧ parent (F.cover e) = parent f) ∧ _
  by_cases hi : F.ContractibleBlock copyCarrier copyEdges parent C (trainCyclicPred i)
  · have hEdge : F.contractingEdge copyCarrier copyEdges parent C hOld
        (trainCyclicPred i) hi = f := by
      apply Sum.inr.inj
      simpa only [projectedLabel, dif_pos hi] using hLabel
    have hWagon : C.connector (trainCyclicPred i) = Sum.inr (parent f) := by
      have hw := (F.contractingEdge_spec copyCarrier copyEdges parent C hOld _ hi).2.2
      rw [hEdge] at hw
      exact hw
    obtain ⟨a, b, ha, hb, _hab⟩ :=
      F.contractible_has_edge_occurrences copyCarrier copyEdges parent C hNormal _ hi
    rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two] at hb
    have hParentA : parent (F.cover a) = parent f := by
      apply OrderOneData.parent_of_edge_wagon_incidence H a (parent f)
      simpa only [ha, hWagon] using C.left_incident (trainCyclicPred i)
    have hParentB : parent (F.cover b) = parent f := by
      apply OrderOneData.parent_of_edge_wagon_incidence H b (parent f)
      have hr := C.right_incident (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two, hb, hWagon] at hr
      exact hr
    exact ⟨⟨b, hb, hParentB⟩, fun _ => ⟨a, ha, hParentA⟩⟩
  · refine ⟨?_, fun h => False.elim (hi h)⟩
    have hProject : F.projectLabel (C.label i) = Sum.inr f := by
      simpa only [projectedLabel, dif_neg hi] using hLabel
    cases hc : C.label i with
    | inl a => simp [hc, projectLabel] at hProject
    | inr e =>
        have hCover : F.cover e = f := by
          apply Sum.inr.inj
          simpa only [hc, projectLabel, Sum.map_inr] using hProject
        exact ⟨e, rfl, congrArg parent hCover⟩

/-- Constant parent for physical projected labels forces the same on
EVERY source occurrence, including both halves of each contracted block. -/
theorem projected_edge_only_constant_parent_false {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hNormal : C.MixedNormalized H)
    (hAccept : C.Acceptable)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (edge : Fin (F.retainedPositions copyCarrier copyEdges parent C).card → F.OldEdge)
    (hLabel : ∀ j, F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inr (edge j))
    (p : P) (hParent : ∀ j, parent (edge j) = p) : False := by
  classical
  have hSource (i : Fin n) :
      ∃ e : F.NewEdge, C.label i = Sum.inr e ∧ parent (F.cover e) = p := by
    by_cases hi : F.ContractibleBlock copyCarrier copyEdges parent C i
    · have hs := (F.contractible_neighbours_retained copyCarrier copyEdges parent C i hi).2
      obtain ⟨j, hj⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C _ hs
      have hprev : trainCyclicPred (F.retainedIndex copyCarrier copyEdges parent C j) = i := by
        rw [hj, trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two]
      have hBlock := (F.projected_edge_source_parents copyCarrier copyEdges parent
        C hOld hNormal j (edge j) (hLabel j)).2
      rw [hprev] at hBlock
      obtain ⟨e, he, hp⟩ := hBlock hi
      exact ⟨e, he, hp.trans (hParent j)⟩
    · obtain ⟨j, hj⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C i hi
      obtain ⟨e, he, hp⟩ := (F.projected_edge_source_parents copyCarrier copyEdges parent
        C hOld hNormal j (edge j) (hLabel j)).1
      rw [hj] at he
      exact ⟨e, he, hp.trans (hParent j)⟩
  choose source hSourceLabel hSourceParent using hSource
  exact C.false_of_edge_only_constant_parent source hSourceLabel p hSourceParent hEdges hAccept

/-- The two-survivor collision is ruled out by the SOURCE obstruction;
source length is arbitrary, and the contraction edge need not be a cover. -/
theorem projected_adjacent_edge_ne_all {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hAccept : C.Acceptable)
    (hNormal : C.MixedNormalized H)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton)
    (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) (f : F.OldEdge)
    (hj : F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inr f)
    (hs : F.projectedLabel copyCarrier copyEdges parent C hOld (cyclicSucc j) = Sum.inr f) :
    False := by
  have hm2 := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
  by_cases hm : 3 ≤ (F.retainedPositions copyCarrier copyEdges parent C).card
  · apply F.projected_adjacent_edge_ne copyCarrier copyEdges parent C hAccept.2.1 hAccept.2.2
      hm (F.retainedIndex copyCarrier copyEdges parent C)
      (F.retainedIndex_not_contractible copyCarrier copyEdges parent C)
      (F.projectedLabel copyCarrier copyEdges parent C hOld)
      (F.projectedLabel_right_incident copyCarrier copyEdges parent C hOld)
      _ j f hj hs
    intro t
    have h := F.projectedLabel_left_incident copyCarrier copyEdges parent C hOld (cyclicSucc t)
    simpa only [trainCyclicPred_cyclicSucc_of_two_le hm2] using h
  · have hmEq : (F.retainedPositions copyCarrier copyEdges parent C).card = 2 := by omega
    apply F.projected_edge_only_constant_parent_false copyCarrier copyEdges parent
      C hOld hNormal hAccept hEdges (fun _ => f) _ (parent f) (fun _ => rfl)
    intro t
    rcases fin_eq_or_succ_of_two hmEq t j with ht | ht
    · rw [ht]; exact hj
    · rw [ht]; exact hs

/-- The canonical projected BigCycle, with no retained-length exception. -/
noncomputable def projectedCycle {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hAccept : C.Acceptable)
    (hNormal : C.MixedNormalized H)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    (O).BigCycle (F.retainedPositions copyCarrier copyEdges parent C).card where
  length_ge_two := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
  label := F.projectedLabel copyCarrier copyEdges parent C hOld
  connector := fun j => C.connector (F.retainedIndex copyCarrier copyEdges parent C j)
  adjacent_ne := by
    intro j hEq
    cases hLabel : F.projectedLabel copyCarrier copyEdges parent C hOld j with
    | inl a =>
        exact F.projected_adjacent_designated_ne copyCarrier copyEdges parent C hOld hNormal
          j a hLabel (hEq.symm.trans hLabel)
    | inr f =>
        exact F.projected_adjacent_edge_ne_all copyCarrier copyEdges parent C hOld hAccept
          hNormal hEdges j f hLabel (hEq.symm.trans hLabel)
  connector_injective := C.connector_injective.comp
    (F.retainedIndex copyCarrier copyEdges parent C).injective
  left_incident := F.projectedLabel_right_incident copyCarrier copyEdges parent C hOld
  right_incident := by
    intro j
    have hm2 := F.retainedPositions_card_two_le copyCarrier copyEdges parent C
    have h := F.projectedLabel_left_incident copyCarrier copyEdges parent C hOld (cyclicSucc j)
    simpa only [trainCyclicPred_cyclicSucc_of_two_le hm2] using h

/-- A1 follows from parent transfer, A2/A3 from edge-sensitive restriction;
only order nonincrease is needed to apply the original cutoff. -/
theorem projectedCycle_acceptable_and_order {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hAccept : C.Acceptable)
    (hNormal : C.MixedNormalized H)
    (hEdges : ∀ e f : F.NewEdge, e ≠ f → (e.1 ∩ f.1).Subsingleton) :
    let B := F.projectedCycle copyCarrier copyEdges parent C hOld hAccept hNormal hEdges
    B.Acceptable ∧ B.twiceOrder ≤ C.twiceOrder := by
  classical
  let B := F.projectedCycle copyCarrier copyEdges parent C hOld hAccept hNormal hEdges
  obtain ⟨_hLength, hOrder, hA2, hA3⟩ :=
    F.filling_canonical_restriction_bounds copyCarrier copyEdges parent C B hAccept (fun _ => rfl)
  refine ⟨⟨?_, hA2, hA3⟩, hOrder⟩
  intro hOne
  by_contra hNone
  have hPhysical (j : Fin (F.retainedPositions copyCarrier copyEdges parent C).card) :
      ∃ f : F.OldEdge, B.label j = Sum.inr f := by
    cases hj : B.label j with
    | inl a => exact False.elim (hNone ⟨j, by simp [OrderOneData.designated, hj]⟩)
    | inr f => exact ⟨f, rfl⟩
  choose edge hLabel using hPhysical
  obtain ⟨p, hParent⟩ := B.orderOne_edge_only_constant_parent O edge hLabel hOne
  exact F.projected_edge_only_constant_parent_false copyCarrier copyEdges parent
    C hOld hNormal hAccept hEdges edge hLabel p hParent

/-- Mixed normalization ensures a designated source position is retained. -/
theorem designated_position_retained {n : ℕ} (C : (H).BigCycle n)
    (hNormal : C.MixedNormalized H) (i : Fin n) (a : I)
    (ha : C.label i = Sum.inl a) :
    ¬ F.ContractibleBlock copyCarrier copyEdges parent C i := by
  intro hi
  obtain ⟨e, _f, he, _⟩ :=
    F.contractible_has_edge_occurrences copyCarrier copyEdges parent C hNormal i hi
  have hbad := ha.symm.trans he
  cases hbad

/-- Every designated occurrence survives with its original label and index. -/
theorem designated_source_projects {n : ℕ} (C : (H).BigCycle n)
    (hOld : (O).LinearPretrain) (hNormal : C.MixedNormalized H)
    (i : Fin n) (a : I) (ha : C.label i = Sum.inl a) :
    ∃ j, F.retainedIndex copyCarrier copyEdges parent C j = i ∧
      F.projectedLabel copyCarrier copyEdges parent C hOld j = Sum.inl a := by
  obtain ⟨j, hj⟩ := F.retainedIndex_surjective copyCarrier copyEdges parent C i
    (F.designated_position_retained copyCarrier copyEdges parent C hNormal i a ha)
  refine ⟨j, hj, ?_⟩
  apply (F.projectedLabel_eq_designated_iff copyCarrier copyEdges parent C hOld hNormal j a).mpr
  rw [hj]
  exact ha
end TrainFilling
end StructuralRamsey.Girth
