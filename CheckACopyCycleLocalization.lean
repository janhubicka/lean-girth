import Girth.ACopyCycleLocalization

open StructuralRamsey.Girth
open StructuralRamsey.Girth.ACopyCycleLocalization

namespace ACopyCycleLocalizationRegression

/-- Transition-only incidence genuinely permits private connectors: both
connectors here lie outside the only carrier. -/
theorem private_connectors_allowed :
    (∀ i j : Fin 2, (fun _ : Fin 2 => ()) i = (fun _ : Fin 2 => ()) j) ∧
    (∀ i : Fin 2, i ∉ (∅ : Set (Fin 2))) := by
  have hGraph : boundaryIncidenceGraph (fun _ : Unit => (∅ : Set (Fin 2))) = ⊥ := by
    ext a b
    cases a <;> cases b <;> simp [boundaryIncidenceGraph]
  constructor
  · apply cyclicOwner_constant_of_acyclic
      (fun _ : Unit => (∅ : Set (Fin 2))) (by decide)
      (fun _ : Fin 2 => ()) (fun i : Fin 2 => i) Function.injective_id
    · intro k hk
      exact (hk rfl).elim
    · rw [hGraph]
      exact SimpleGraph.isAcyclic_bot
  · simp

/-- Distinct labels with the same two-point carrier violate labelled girth
already at cutoff two.  The helper must not collapse them as equal sets. -/
theorem duplicate_carriers_fail_labelled_girth :
    ¬ LabelledGirthGT (fun _ : Bool => (Set.univ : Set (Fin 2))) 2 := by
  intro h
  have hSub := labelledGirthGT_two_pairwise_subsingleton h false true (by decide)
  have heq : (0 : Fin 2) = 1 := hSub (by simp) (by simp)
  exact (by decide : (0 : Fin 2) ≠ 1) heq

/-- Forgetting those labels collapses the family to one physical edge and
loses the obstruction; the two girth statements are deliberately different. -/
theorem duplicate_carriers_collapsed_girth (g : ℕ) :
    GirthGT (Set.range (fun _ : Bool => (Set.univ : Set (Fin 2)))) g := by
  apply girthGT_of_edgeFamily_subsingleton
  rintro a ⟨_, rfl⟩ b ⟨_, rfl⟩
  rfl

/-- Without distinct connectors, two different owners can traverse a single
point back and forth even though the labelled incidence graph is acyclic. -/
theorem repeated_connector_counterexample :
    (boundaryIncidenceGraph (fun _ : Fin 2 => (Set.univ : Set Unit))).IsAcyclic ∧
    (∀ _k : Fin 2, () ∈ (Set.univ : Set Unit) ∧ () ∈ (Set.univ : Set Unit)) ∧
    ¬ (∀ i j : Fin 2, i = j) := by
  have hGirth : LabelledGirthGT (fun _ : Fin 2 => (Set.univ : Set Unit)) 2 := by
    rintro ⟨C, _⟩
    let i : Fin C.length := ⟨0, by have := C.hlength; omega⟩
    have hEq : i = cyclicSucc i := C.vertex_injective (Subsingleton.elim _ _)
    exact RawCyclicIncidenceData.cyclicSucc_ne_self_of_two_le C.hlength i hEq.symm
  refine ⟨labelledGirthGT_incidence_acyclic_of_card _ 2 (by decide) (by decide) hGirth,
    fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (h 0 1)

end ACopyCycleLocalizationRegression

#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.cyclicOwner_constant_of_acyclic
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.cyclicOwner_constant_of_used_acyclic
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.used_card_le_length
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.used_card_lt_length_of_not_injective
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.cyclicOwner_constant_of_girth_of_used_card
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.labelledCycle_owner_constant_of_girth
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.singleton_refinement_localizes
#print axioms StructuralRamsey.Girth.ACopyCycleLocalization.retainedCut_localizes
#print axioms ACopyCycleLocalizationRegression.private_connectors_allowed
#print axioms ACopyCycleLocalizationRegression.duplicate_carriers_fail_labelled_girth
#print axioms ACopyCycleLocalizationRegression.duplicate_carriers_collapsed_girth
#print axioms ACopyCycleLocalizationRegression.repeated_connector_counterexample
