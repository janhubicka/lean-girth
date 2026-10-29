import Girth.TrainRecursiveWitnessInitialParameters
import Girth.TrainRecursiveWitnessInitialSupreme
import Girth.ForestCyclicSwitching

/-!
# Cycles at a proper initial cut stay in one component

The complete physical initial edge type is already identified with
component/target-edge pairs.  At a proper cut, related edges have the same
component, so every initial wagon has a well-defined component and target
wagon coordinate.  Incidence with either kind of connector preserves that
component.  Cyclic connectedness therefore localizes every genuine BigCycle,
without an acceptability or system-girth hypothesis.

When a designated label occurs, the existing literal identity-plan theorem
makes that label supreme.  The exclusion of edge-only cycles requires target
horizontal-cut girth and is handled separately.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P I : Type v}

section Coordinates

variable (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
variable (B : RelStructure L VB) (β : I → VB ↪ P) [Nonempty I]

/-- The component and target edge of an actual initial physical edge. -/
noncomputable def initialEdgeCoordinates
    (edge : OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) :
    I × OldACarrierEdge A B :=
  (initialPhysicalEdgeEquiv A hA B β).symm edge

@[simp] theorem initialEdgeCoordinates_physical
    (i : I) (edge : OldACarrierEdge A B) :
    initialEdgeCoordinates A hA B β (initialPhysicalEdge A B β (i, edge)) =
      (i, edge) :=
  (initialPhysicalEdgeEquiv A hA B β).symm_apply_apply (i, edge)

/-- Every vertex of an initial edge has that edge's component coordinate. -/
theorem initialEdgeCoordinates_mem
    (edge : OldACarrierEdge A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    (x : I × VB) (hx : x ∈ edge.1) :
    x.1 = (initialEdgeCoordinates A hA B β edge).1 := by
  obtain ⟨⟨i, e⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β edge
  rw [initialEdgeCoordinates_physical]
  obtain ⟨b, _, hb⟩ := hx
  exact (congrArg Prod.fst hb).symm

variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
variable (μ : Fin (m + 1)) (hμ : μ.val < m)

/-- The proper-cut quotient retains both its literal initial component and
its target wagon label, even when physical wagon carriers happen to agree. -/
noncomputable def initialWagonCoordinates :
    Quotient ((initialTrain A hA B β T hm).wagonSetoid μ) →
      I × Quotient (T.wagonSetoid μ) :=
  Quotient.lift
    (fun edge =>
      ((initialEdgeCoordinates A hA B β edge).1,
        Quotient.mk (T.wagonSetoid μ) (initialEdgeCoordinates A hA B β edge).2))
    (by
      intro a b hab
      obtain ⟨⟨i, e⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β a
      obtain ⟨⟨j, f⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β b
      simp only [initialEdgeCoordinates_physical]
      rcases (initialTrain_rel_iff A hA B β T hm i j μ e f).mp hab with
        htop | ⟨hij, hrel⟩
      · exact (Nat.ne_of_lt hμ htop).elim
      · exact Prod.ext hij (Quotient.sound hrel))

@[simp] theorem initialWagonCoordinates_physical
    (i : I) (e : OldACarrierEdge A B) :
    initialWagonCoordinates A hA B β T hm μ hμ
      (Quotient.mk ((initialTrain A hA B β T hm).wagonSetoid μ)
        (initialPhysicalEdge A B β (i, e))) =
      (i, Quotient.mk (T.wagonSetoid μ) e) := by
  simp [initialWagonCoordinates]

/-- Distinct initial wagons retain distinct component/target-wagon pairs. -/
theorem initialWagonCoordinates_injective :
    Function.Injective (initialWagonCoordinates A hA B β T hm μ hμ) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
          obtain ⟨⟨i, e⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β a
          obtain ⟨⟨j, f⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β b
          simp only [initialWagonCoordinates_physical] at hpq
          apply Quotient.sound
          exact (initialTrain_rel_iff A hA B β T hm i j μ e f).mpr
            (Or.inr ⟨congrArg Prod.fst hpq, Quotient.exact (congrArg Prod.snd hpq)⟩)

/-- The full initial wagon carrier is the tagged target carrier specified by
the quotient coordinates. -/
theorem initialWagonCoordinates_carrier
    (p : Quotient ((initialTrain A hA B β T hm).wagonSetoid μ)) :
    (initialTrain A hA B β T hm).wagonClassCarrier (fun edge => edge.1) μ p =
      (fun b : VB => ((initialWagonCoordinates A hA B β T hm μ hμ p).1, b)) ''
        T.wagonClassCarrier (fun edge => edge.1) μ
          (initialWagonCoordinates A hA B β T hm μ hμ p).2 := by
  induction p using Quotient.inductionOn with
  | h edge =>
      obtain ⟨⟨i, e⟩, rfl⟩ := initialPhysicalEdge_surjective A hA B β edge
      rw [initialWagonCoordinates_physical]
      exact initialTrain_wagonCarrier A hA B β T hm i μ hμ e

end Coordinates

section Selected

variable (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (family : Set (RelStructure.Embedding B D)) [Nonempty family]

set_option quotPrecheck false

local notation "β" => (fun b : family => b.1.toFunctionEmbedding)
local notation "C₀" => StructuralRamsey.Partite.Initial.picture B β
local notation "Edge" => OldACarrierEdge A (C₀).toRelStructure
local notation "Copy" => {q : DesignatedCopy B D C₀ family // q ∈ initialSelected B D family}

/-- Literal component ownership of every selected copy and actual edge label. -/
noncomputable def initialLabelComponent : Copy ⊕ Edge → family
  | .inl q => ⟨q.1.base, q.1.base_mem⟩
  | .inr edge => (initialEdgeCoordinates A hA B β edge).1

theorem initialLabelComponent_carrier
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (μ : Fin (m + 1)) (label : Copy ⊕ Edge) (x : family × VB)
    (hx : x ∈ (selectedPictureOrderOneData A B D C₀ family
      (initialSelected B D family) (initialTrain A hA B β T hm) μ).carrier label) :
    x.1 = initialLabelComponent A hA B D family label := by
  cases label with
  | inr edge => exact initialEdgeCoordinates_mem A hA B β edge x hx
  | inl q =>
      rcases q with ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := hq
      obtain ⟨v, hv⟩ := hx
      exact (congrArg Prod.fst hv).symm

theorem initialLabelComponent_of_mem_edges
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (μ : Fin (m + 1)) (label : Copy ⊕ Edge) (edge : Edge)
    (he : edge ∈ (selectedPictureOrderOneData A B D C₀ family
      (initialSelected B D family) (initialTrain A hA B β T hm) μ).edges label) :
    (initialEdgeCoordinates A hA B β edge).1 =
      initialLabelComponent A hA B D family label := by
  cases label with
  | inr f =>
      have h : edge = f := he
      subst f
      rfl
  | inl q =>
      obtain ⟨a, ha⟩ := edge.2
      obtain ⟨u⟩ := (inferInstance : Nonempty UA)
      have hx : a u ∈ edge.1 := by rw [ha]; exact ⟨u, rfl⟩
      have hcopy := initialLabelComponent_carrier A hA B D family T hm μ
        (Sum.inl q) (a u) (he hx)
      exact (initialEdgeCoordinates_mem A hA B β edge (a u) hx).symm.trans hcopy

variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
variable (μ : Fin (m + 1)) (hμ : μ.val < m)

local notation "T₀" => initialTrain A hA B β T hm
local notation "O" => selectedPictureOrderOneData A B D C₀ family
  (initialSelected B D family) T₀ μ

/-- The component coordinate of either kind of initial connector. -/
noncomputable def initialConnectorComponent :
    (family × VB) ⊕ Quotient ((T₀).wagonSetoid μ) → family
  | .inl x => x.1
  | .inr p => (initialWagonCoordinates A hA B β T hm μ hμ p).1

/-- Vertex and wagon connectors have the same component as every incident
label.  The proper-cut condition is essential for wagon connectors. -/
theorem initial_incident_component
    (label : Copy ⊕ Edge)
    (connector : (family × VB) ⊕ Quotient ((T₀).wagonSetoid μ))
    (hIncident : (O).Incident label connector) :
    initialLabelComponent A hA B D family label =
      initialConnectorComponent A hA B D family T hm μ hμ connector := by
  cases connector with
  | inl x =>
      exact (initialLabelComponent_carrier A hA B D family T hm μ label x hIncident).symm
  | inr p =>
      obtain ⟨edge, he, hp⟩ := hIncident
      have h := initialLabelComponent_of_mem_edges A hA B D family T hm μ label edge he
      change initialLabelComponent A hA B D family label =
        (initialWagonCoordinates A hA B β T hm μ hμ p).1
      rw [← hp]
      exact h.symm

include hμ

/-- All labels of a genuine cycle at a proper initial cut have one literal
component.  Acceptability is unnecessary for this localization. -/
theorem initialCycle_components_eq
    {n : ℕ} (C : (O).BigCycle n) (i j : Fin n) :
    initialLabelComponent A hA B D family (C.label i) =
      initialLabelComponent A hA B D family (C.label j) := by
  let owner : Fin n → family := fun k => initialLabelComponent A hA B D family (C.label k)
  have hStep : ∀ k : Fin n, owner k = owner (cyclicSucc k) := by
    intro k
    exact (initial_incident_component A hA B D family T hm μ hμ
      (C.label k) (C.connector k) (C.left_incident k)).trans
      (initial_incident_component A hA B D family T hm μ hμ
        (C.label (cyclicSucc k)) (C.connector k) (C.right_incident k)).symm
  let zero : Fin n := ⟨0, by have := C.length_ge_two; omega⟩
  have hAll : ∀ k : Fin n, owner k = owner (cyclicSucc zero) := by
    intro k
    by_cases hk : k = zero
    · subst k
      exact hStep zero
    · exact cyclicOwner_eq_off_singleton C.length_ge_two owner zero
        (fun k _ _ => hStep k) k hk
  exact (hAll i).trans (hAll j).symm

/-- Every complete occurrence carrier is contained in the same actual
initial target component. -/
theorem initialCycle_localizes
    {n : ℕ} (C : (O).BigCycle n) :
    ∃ b : family, ∀ j : Fin n,
      (O).carrier (C.label j) ⊆ copyCarrier (initialDesignatedCopy B D family b).embedding := by
  let zero : Fin n := ⟨0, by have := C.length_ge_two; omega⟩
  let b := initialLabelComponent A hA B D family (C.label zero)
  refine ⟨b, ?_⟩
  intro j x hx
  have hfirst := initialLabelComponent_carrier A hA B D family T hm μ (C.label j) x hx
  have howner := initialCycle_components_eq A hA B D family T hm μ hμ C j zero
  exact ⟨x.2, Prod.ext (hfirst.trans howner).symm rfl⟩

/-- A cycle with a designated occurrence has a literal globally legal
supreme plan at every proper initial cut.  Only edge-only cycles remain. -/
theorem initialCycle_hasSupreme_of_designated [Nonempty VB]
    {n : ℕ} (C : (O).BigCycle n)
    (hDesignated : ∃ k : Fin n, (O).designated (C.label k)) :
    C.HasSimultaneousSupreme := by
  obtain ⟨k, hk⟩ := hDesignated
  cases hLabel : C.label k with
  | inr edge => simp only [hLabel, OrderOneData.designated] at hk
  | inl q =>
      rcases q with ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := hq
      have hContain : ∀ j : Fin n, (O).carrier (C.label j) ⊆
          copyCarrier (initialDesignatedCopy B D family b).embedding := by
        intro j x hx
        have hfirst := initialLabelComponent_carrier A hA B D family T hm μ (C.label j) x hx
        have howner := initialCycle_components_eq A hA B D family T hm μ hμ C j k
        rw [hLabel] at howner
        exact ⟨x.2, Prod.ext (hfirst.trans howner).symm rfl⟩
      exact C.hasSimultaneousSupreme_of_hasSupremeAt _ k
        (initialCycle_hasSupremeAt_of_contained A B D family T₀ μ C b k hLabel hContain)

end Selected
end StructuralRamsey.Girth.TrainRecursiveWitness
