import Girth.TrainSimultaneousSupreme

/-!
# Circulation: enlarging designated subcopy cycles

The first step of Section 13's subcopy-restriction argument replaces each
target label by the designated copy containing it. The map on designated
labels need not be injective: several disjoint targets can lie in one old
copy. Nevertheless it does not identify adjacent labels of a big cycle,
because two adjacent targets share a vertex or a wagon connector.

This file proves that enlargement is a genuine big cycle, with exactly the
same connector word, order and acceptability. Ambient edges and their wagon
partition are unchanged; in particular no ambient-edge pruning or inference
from equality of wagon carriers occurs. An old full-system-girth bound then
supplies an indexed supreme parent with an actual target occurrence in the
original cycle.

This is the projection step, not the full subcopy-restriction theorem.
Replacing old supreme pieces by target edges and pulling the resulting
global plan back still requires the target's coverage, strong-inducedness
and inter-wagon intersection hypotheses from the manuscript.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v

variable {V E I J P : Type v}

/-- Target copies inside the designated copies of a fixed physical system.
Only targets with the same parent must be disjoint in both kinds of
connector. This is inherited from the manuscript's vertex- and
wagon-disjoint components; no injectivity of `containingCopy` is assumed. -/
structure DesignatedSubcopyFamily (D : OrderOneData V E I P) (J : Type v) where
  containingCopy : J → I
  copyCarrier : J → Set V
  copyEdges : J → Set E
  carrier_subset : ∀ j, copyCarrier j ⊆ D.copyCarrier (containingCopy j)
  edges_subset : ∀ j, copyEdges j ⊆ D.copyEdges (containingCopy j)
  siblings_vertex_disjoint : ∀ j k, j ≠ k → containingCopy j = containingCopy k →
    Disjoint (copyCarrier j) (copyCarrier k)
  siblings_wagon_disjoint : ∀ j k, j ≠ k → containingCopy j = containingCopy k →
    ∀ e f, e ∈ copyEdges j → f ∈ copyEdges k → D.parent e ≠ D.parent f

namespace DesignatedSubcopyFamily

variable {D : OrderOneData V E I P} (S : DesignatedSubcopyFamily D J)

/-- Change only designated carriers and their edge families. Every ambient
edge, edge carrier and wagon label is retained literally. -/
def target : OrderOneData V E J P where
  edgeCarrier := D.edgeCarrier
  copyCarrier := S.copyCarrier
  copyEdges := S.copyEdges
  parent := D.parent

/-- Enlarge a target label to its old designated parent; preserve actual
edge labels. Unlike a physical embedding this need not be injective. -/
def enlargeLabel : J ⊕ E → I ⊕ E
  | .inl j => .inl (S.containingCopy j)
  | .inr e => .inr e

@[simp] theorem designated_enlargeLabel (a : J ⊕ E) :
    D.designated (S.enlargeLabel a) ↔ S.target.designated a := by
  cases a <;> rfl

/-- Every target incidence remains an incidence of its containing label. -/
theorem incident_enlargeLabel (a : J ⊕ E) (c : V ⊕ P)
    (h : S.target.Incident a c) : D.Incident (S.enlargeLabel a) c := by
  cases a with
  | inl j =>
      cases c with
      | inl x => exact S.carrier_subset j h
      | inr p =>
          obtain ⟨e, he, hp⟩ := h
          exact ⟨e, S.edges_subset j he, hp⟩
  | inr e => exact h

/-- Two distinct targets with one old designated parent cannot meet the
same connector, whether that connector is a vertex or a wagon. -/
theorem siblings_not_incident (j k : J) (hjk : j ≠ k)
    (hParent : S.containingCopy j = S.containingCopy k) (c : V ⊕ P)
    (hj : S.target.Incident (.inl j) c)
    (hk : S.target.Incident (.inl k) c) : False := by
  cases c with
  | inl x =>
      exact (Set.disjoint_left.mp (S.siblings_vertex_disjoint j k hjk hParent)) hj hk
  | inr p =>
      obtain ⟨e, he, hep⟩ := hj
      obtain ⟨f, hf, hfp⟩ := hk
      exact S.siblings_wagon_disjoint j k hjk hParent e f he hf (hep.trans hfp.symm)

/-- Enlargement is injective on labels incident with any fixed connector.
This local assertion is exactly what adjacent-label distinctness needs. -/
theorem enlargeLabel_eq_of_incident (a b : J ⊕ E) (c : V ⊕ P)
    (ha : S.target.Incident a c) (hb : S.target.Incident b c)
    (h : S.enlargeLabel a = S.enlargeLabel b) : a = b := by
  cases a with
  | inl j =>
      cases b with
      | inl k =>
          have hParent : S.containingCopy j = S.containingCopy k := Sum.inl.inj h
          by_cases hjk : j = k
          · exact congrArg Sum.inl hjk
          · exact False.elim (S.siblings_not_incident j k hjk hParent c ha hb)
      | inr e => cases h
  | inr e =>
      cases b with
      | inl k => cases h
      | inr f => exact congrArg Sum.inr (Sum.inr.inj h)

/-- The actual cycle obtained by enlarging every designated target label.
It retains every occurrence and every connector at its original index. -/
def enlargeCycle {n : ℕ} (C : S.target.BigCycle n) : D.BigCycle n where
  length_ge_two := C.length_ge_two
  label := fun i => S.enlargeLabel (C.label i)
  connector := C.connector
  adjacent_ne := by
    intro i h
    exact C.adjacent_ne i (S.enlargeLabel_eq_of_incident
      (C.label i) (C.label (cyclicSucc i)) (C.connector i)
      (C.left_incident i) (C.right_incident i) h)
  connector_injective := C.connector_injective
  left_incident := fun i =>
    S.incident_enlargeLabel (C.label i) (C.connector i) (C.left_incident i)
  right_incident := fun i =>
    S.incident_enlargeLabel (C.label (cyclicSucc i)) (C.connector i)
      (C.right_incident i)

@[simp] theorem enlargeCycle_connector {n : ℕ} (C : S.target.BigCycle n)
    (i : Fin n) : (S.enlargeCycle C).connector i = C.connector i := rfl

@[simp] theorem enlargeCycle_label {n : ℕ} (C : S.target.BigCycle n)
    (i : Fin n) : (S.enlargeCycle C).label i = S.enlargeLabel (C.label i) := rfl

/-- The entire cyclic connector word is retained, including at length two. -/
theorem enlargeCycle_connector_word {n : ℕ} (C : S.target.BigCycle n) :
    List.ofFn (S.enlargeCycle C).connector = List.ofFn C.connector := rfl

/-- No order estimate is needed: enlargement preserves order exactly. -/
@[simp] theorem enlargeCycle_twiceOrder {n : ℕ} (C : S.target.BigCycle n) :
    (S.enlargeCycle C).twiceOrder = C.twiceOrder := rfl

@[simp] theorem enlargeCycle_A1_iff {n : ℕ} (C : S.target.BigCycle n) :
    (S.enlargeCycle C).A1 ↔ C.A1 := by
  simp only [BigCycle.A1, S.enlargeCycle_twiceOrder, S.enlargeCycle_label,
    S.designated_enlargeLabel]

/-- A2 is identical, including the ambient no-common-edge clause: the
ambient edge set and wagon partition were not restricted. -/
@[simp] theorem enlargeCycle_A2_iff {n : ℕ} (C : S.target.BigCycle n) :
    (S.enlargeCycle C).A2 ↔ C.A2 := Iff.rfl

@[simp] theorem enlargeCycle_A3_iff {n : ℕ} (C : S.target.BigCycle n) :
    (S.enlargeCycle C).A3 ↔ C.A3 := Iff.rfl

/-- The enlargement step preserves all three acceptability clauses,
without assuming any system-girth or linearity bound. -/
theorem enlargeCycle_acceptable_iff {n : ℕ} (C : S.target.BigCycle n) :
    (S.enlargeCycle C).Acceptable ↔ C.Acceptable := by
  simp only [BigCycle.Acceptable, S.enlargeCycle_A1_iff,
    S.enlargeCycle_A2_iff, S.enlargeCycle_A3_iff]

/-- Physical linearity is unchanged because only designated labels changed. -/
theorem target_linearPretrain_iff : S.target.LinearPretrain ↔ D.LinearPretrain := Iff.rfl

/-- An old supreme occurrence identifies an actual retained target
occurrence of the original cycle. The result retains its index and its
genuine globally legal supreme plan in the enlarged cycle.

The conclusion intentionally concerns the parent label. Turning it into a
supreme target requires the subsequent geometric restriction argument. -/
theorem enlargeCycle_supreme_parent_of_fullSystemGirth
    {g n : ℕ} (hGirth : D.FullSystemGirthGT g) (C : S.target.BigCycle n)
    (hAccept : C.Acceptable) (hOrder : C.twiceOrder ≤ 2 * g) :
    ∃ (k : Fin n) (j : J), C.label k = Sum.inl j ∧
      (S.enlargeCycle C).HasSupremeAt D k := by
  have hSup := hGirth.2 n (S.enlargeCycle C)
    ((S.enlargeCycle_acceptable_iff C).2 hAccept)
    (by simpa only [S.enlargeCycle_twiceOrder] using hOrder)
  obtain ⟨k, hk, pieces, hValid, hGlobal⟩ := hSup
  cases hLabel : C.label k with
  | inl j => exact ⟨k, j, hLabel, hk, pieces, hValid, hGlobal⟩
  | inr e =>
      have : False := by
        simpa [enlargeCycle, enlargeLabel, hLabel, designated] using hk
      exact this.elim

end DesignatedSubcopyFamily
end StructuralRamsey.Girth.OrderOneData
