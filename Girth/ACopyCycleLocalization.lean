import Girth.TrainRecursiveRefinementGlobalCutGirth

set_option autoImplicit false

/-!
# Reusable localization of cyclic owner words

Only transitions between different owner labels require incidence.  Connectors
inside a constant run may be private and need not lie in either carrier.  The
finite range keeps labels distinct even when their vertex carriers coincide.

The singleton-refinement and retained-cut wrappers below replay their existing
geometric arguments through this common lemma.  They do not invoke the old
localization theorems or assume the ordinary girth conclusion being proved.
-/

namespace StructuralRamsey.Girth.ACopyCycleLocalization

universe v
variable {V I E Part : Type v}

/-- A cyclic word with distinct connectors cannot change labels in an acyclic
labelled incidence graph.  Incidence is needed only at genuine changes. -/
theorem cyclicOwner_constant_of_acyclic
    (carrier : I → Set V) {n : ℕ} (hn : 2 ≤ n)
    (owner : Fin n → I) (connector : Fin n → V)
    (hConnector : Function.Injective connector)
    (hBoundary : ∀ k, owner k ≠ owner (cyclicSucc k) →
      connector k ∈ carrier (owner k) ∧
      connector k ∈ carrier (owner (cyclicSucc k)))
    (hAcyclic : (boundaryIncidenceGraph carrier).IsAcyclic) :
    ∀ i j, owner i = owner j := by
  by_contra hConstant
  push Not at hConstant
  let raw : RawCyclicIncidenceData carrier := {
    length := n
    hlength := hn
    label := owner
    connector := connector
    connector_injective := hConnector
    boundary_mem := hBoundary
    nonconstant := hConstant
  }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic raw.compress

/-- It is enough that the incidence graph on the labels actually used is
acyclic; no condition is imposed on the unused ambient carriers. -/
theorem cyclicOwner_constant_of_used_acyclic
    (carrier : I → Set V) {n : ℕ} (hn : 2 ≤ n)
    (owner : Fin n → I) (connector : Fin n → V)
    (hConnector : Function.Injective connector)
    (hBoundary : ∀ k, owner k ≠ owner (cyclicSucc k) →
      connector k ∈ carrier (owner k) ∧
      connector k ∈ carrier (owner (cyclicSucc k)))
    (hAcyclic : (boundaryIncidenceGraph
      (fun p : Set.range owner => carrier p.val)).IsAcyclic) :
    ∀ i j, owner i = owner j := by
  let picked : Fin n → Set.range owner := fun i => ⟨owner i, ⟨i, rfl⟩⟩
  have h := cyclicOwner_constant_of_acyclic
    (fun p : Set.range owner => carrier p.val) hn picked connector hConnector
    (fun k hk => hBoundary k (fun heq => hk (Subtype.ext heq))) hAcyclic
  exact fun i j => congrArg Subtype.val (h i j)

/-- Cardinality of the used labels never exceeds the length of the word. -/
theorem used_card_le_length {n : ℕ} (owner : Fin n → I) :
    Nat.card (Set.range owner) ≤ n := by
  classical
  let picked : Fin n → Set.range owner := fun i => ⟨owner i, ⟨i, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  have := Finite.of_surjective picked hOnto
  let := Fintype.ofFinite (Set.range owner)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_surjective picked hOnto

/-- A repeated owner saves one unit in the used-label bound. -/
theorem used_card_lt_length_of_not_injective {n : ℕ} (owner : Fin n → I)
    (hNotInjective : ¬ Function.Injective owner) :
    Nat.card (Set.range owner) < n := by
  classical
  let picked : Fin n → Set.range owner := fun i => ⟨owner i, ⟨i, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  have := Finite.of_surjective picked hOnto
  let := Fintype.ofFinite (Set.range owner)
  have hPicked : ¬ Function.Injective picked := by
    intro h
    apply hNotInjective
    exact fun i j hij => h (Subtype.ext hij)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_lt_of_surjective_not_injective picked hOnto hPicked

/-- Girth greater than `g` makes the used incidence graph acyclic when at
most `g` labels occur.  Total ambient finiteness is not required. -/
theorem cyclicOwner_constant_of_girth_of_used_card
    (carrier : I → Set V) {n : ℕ} (hn : 2 ≤ n)
    (owner : Fin n → I) (connector : Fin n → V)
    (hConnector : Function.Injective connector)
    (hBoundary : ∀ k, owner k ≠ owner (cyclicSucc k) →
      connector k ∈ carrier (owner k) ∧
      connector k ∈ carrier (owner (cyclicSucc k)))
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hCard : Nat.card (Set.range owner) ≤ g) :
    ∀ i j, owner i = owner j := by
  classical
  let picked : Fin n → Set.range owner := fun i => ⟨owner i, ⟨i, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  have := Finite.of_surjective picked hOnto
  let := Fintype.ofFinite (Set.range owner)
  apply cyclicOwner_constant_of_used_acyclic carrier hn owner connector
    hConnector hBoundary
  apply labelledGirthGT_incidence_acyclic_of_card _ g hg
  · simpa only [Nat.card_eq_fintype_card] using hCard
  · exact labelledGirthGT_of_injective_reindex carrier Subtype.val
      Subtype.val_injective g hGirth

/-- Physical cycle specialization: containment supplies transition incidence,
and the cycle length bounds the number of distinct carriers used. -/
theorem labelledCycle_owner_constant_of_girth
    {edge : E → Set V} (C : LabelledBergeCycle edge)
    (owner : Fin C.length → I) (carrier : I → Set V)
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (owner i))
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ g) :
    ∀ i j, owner i = owner j :=
  cyclicOwner_constant_of_girth_of_used_card carrier C.hlength owner C.vertex
    C.vertex_injective
    (fun i _ => ⟨hContained i (C.left_mem i),
      hContained (cyclicSucc i) (C.right_mem i)⟩)
    g hg hGirth ((used_card_le_length owner).trans hLength)

/-- Singleton-refinement application.  Actual edge transversality forces a
repeated child; the common cyclic-word lemma then supplies localization. -/
theorem singleton_refinement_localizes
    {edge : E → Set V} (C : LabelledBergeCycle edge)
    (child : Fin C.length → I) (carrier : I → Set V)
    (part : V → Part) (allowed : Set Part) (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : I, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ g + 1) :
    ∀ i j, child i = child j := by
  have hRepeat := C.child_not_injective_of_singleton_intersections
    child carrier part allowed hAllowed hEdgePart hContained hIntersection
  have hCardLt := used_card_lt_length_of_not_injective child hRepeat
  exact cyclicOwner_constant_of_girth_of_used_card carrier C.hlength child C.vertex
    C.vertex_injective
    (fun i _ => ⟨hContained i (C.left_mem i),
      hContained (cyclicSucc i) (C.right_mem i)⟩)
    g hg hGirth (by omega)

/-- Retained-cut application uses genuine quotient wagon labels, including
distinct classes with equal carriers; all ambient physical edges remain. -/
theorem retainedCut_localizes
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set V) (μ : Fin (m + 1))
    (q : ℕ) (hq : 2 ≤ q)
    (hCut : LabelledGirthGT (T.wagonClassCarrier edge μ) q)
    (C : LabelledBergeCycle edge) (hLength : C.length ≤ q) :
    ∀ i j, T.rel μ (C.label i) (C.label j) := by
  let owner : Fin C.length → Quotient (T.wagonSetoid μ) :=
    fun i => Quotient.mk (T.wagonSetoid μ) (C.label i)
  have h := labelledCycle_owner_constant_of_girth C owner
    (T.wagonClassCarrier edge μ)
    (fun i x hx => ⟨C.label i, (T.equivalent μ).refl _, hx⟩)
    q hq hCut hLength
  exact fun i j => Quotient.exact (h i j)

end StructuralRamsey.Girth.ACopyCycleLocalization
