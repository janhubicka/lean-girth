import Girth.ACopyChartCoverage

open StructuralRamsey StructuralRamsey.RelStructure StructuralRamsey.Girth
open StructuralRamsey.Girth.ACopyChartCoverage

namespace ACopyChartCoverageRegression

def binaryLanguage : RelLanguage where
  Symbol := Unit
  arity := fun _ => 2

def complete (X : Type) : RelStructure binaryLanguage X where
  rel := fun _ _ => True

theorem complete_irreducible (X : Type) : (complete X).Irreducible := by
  intro x y _
  exact ⟨(), ![x, y], ⟨0, by decide⟩, ⟨1, by decide⟩, trivial, rfl, rfl⟩

def duplicatedChart (_ : Bool) : Embedding (complete Bool) (complete Bool) :=
  Embedding.id _

theorem duplicatedChart_coverage : CoversIrreducibles duplicatedChart := by
  intro S _
  exact ⟨false, fun x _ => ⟨x, rfl⟩⟩

def firstOccurrence : Occurrence (complete Bool) (fun _ : Bool => complete Bool) :=
  ⟨false, Embedding.id _⟩

def secondOccurrence : Occurrence (complete Bool) (fun _ : Bool => complete Bool) :=
  ⟨true, Embedding.id _⟩

/-- Equal chart images do not turn their labels into equal labels. -/
theorem duplicate_occurrences_distinct : firstOccurrence ≠ secondOccurrence := by
  intro h
  have := congrArg Sigma.fst h
  exact Bool.false_ne_true this

/-- Physical occurrences, in contrast, are identified by their carriers. -/
theorem duplicate_occurrences_identified :
    Quotient.mk (occurrenceSetoid duplicatedChart) firstOccurrence =
      Quotient.mk (occurrenceSetoid duplicatedChart) secondOccurrence := by
  apply (occurrence_quotient_eq_iff _ _ _).mpr
  rfl

def swap : Embedding (complete Bool) (complete Bool) where
  toFun := Bool.not
  injective := by
    intro x y h
    have := congrArg Bool.not h
    simpa only [Bool.not_not] using this
  map_rel_iff := fun _ _ => Iff.rfl

theorem automorphic_embeddings_distinct : swap ≠ Embedding.id (complete Bool) := by
  intro h
  have he := congrArg (fun f : Embedding (complete Bool) (complete Bool) => f false) h
  exact Bool.false_ne_true he.symm

/-- The exact-support quotient works for a nonrigid irreducible type. -/
theorem automorphic_occurrences_identified :
    Quotient.mk (occurrenceSetoid duplicatedChart)
        (⟨false, swap⟩ : Occurrence (complete Bool) (fun _ : Bool => complete Bool)) =
      Quotient.mk (occurrenceSetoid duplicatedChart) firstOccurrence := by
  apply (occurrence_quotient_eq_iff _ _ _).mpr
  ext x
  constructor
  · intro _
    exact ⟨x, rfl⟩
  · intro _
    exact ⟨!x, Bool.not_not x⟩

theorem duplicatedChart_exact_support :
    Set.range (occurrenceCarrier (A := complete Bool) duplicatedChart) =
      supportCopies (complete Bool) (complete Bool) :=
  occurrenceCarriers_eq_supportCopies duplicatedChart duplicatedChart_coverage
    (complete_irreducible Bool)

theorem finite_actual_copy_is_chart (b : Embedding (complete Bool) (complete Bool)) :
    ∃ i, SameCopy b (duplicatedChart i) :=
  actual_copy_eq_chart duplicatedChart duplicatedChart_coverage
    (complete_irreducible Bool) b

def emptyLanguage : RelLanguage where
  Symbol := PEmpty
  arity := PEmpty.elim

def discrete (X : Type) : RelStructure emptyLanguage X where
  rel := fun R => by cases R

def singletonChart (b : Bool) : Embedding (discrete Unit) (discrete Bool) where
  toFun := fun _ => b
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff := fun R => PEmpty.elim R

def emptyToUnit : Embedding (discrete PEmpty) (discrete Unit) where
  toFun := PEmpty.elim
  injective := fun x => PEmpty.elim x
  map_rel_iff := fun R => PEmpty.elim R

theorem singleton_free_amalgam :
    IsFreeAmalgam emptyToUnit emptyToUnit (singletonChart false) (singletonChart true) := by
  constructor
  · intro b
    cases b
    · exact Or.inl ⟨(), rfl⟩
    · exact Or.inr ⟨(), rfl⟩
  · intro a b
    constructor
    · intro h
      exact (Bool.false_ne_true h).elim
    · rintro ⟨d, _⟩
      exact PEmpty.elim d
  · intro R
    exact PEmpty.elim R

theorem singleton_charts_cover_irreducibles : CoversIrreducibles singletonChart := by
  have hOne : CoversIrreducibles (fun _ : Unit => Embedding.id (discrete Unit)) := by
    intro S _
    exact ⟨(), fun x _ => ⟨x, rfl⟩⟩
  intro S hS
  rcases coversIrreducibles_freeAmalgam singleton_free_amalgam
    (fun _ : Unit => Embedding.id (discrete Unit))
    (fun _ : Unit => Embedding.id (discrete Unit)) hOne hOne S hS with h | h
  · obtain ⟨_, h⟩ := h
    exact ⟨false, h⟩
  · obtain ⟨_, h⟩ := h
    exact ⟨true, h⟩

theorem discrete_pair_not_irreducible : ¬ (discrete Bool).Irreducible := by
  intro h
  obtain ⟨R, _⟩ := h Bool.false_ne_true
  exact PEmpty.elim R

/-- Without irreducibility, a physical copy can span distinct full charts
even though every induced irreducible is covered. -/
theorem reducible_copy_missing_from_occurrences :
    Set.univ ∈ supportCopies (discrete Bool) (discrete Bool) ∧
      Set.univ ∉ Set.range (occurrenceCarrier (A := discrete Bool) singletonChart) := by
  constructor
  · refine ⟨Embedding.id _, ?_⟩
    ext x
    exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Set.mem_univ x⟩
  · rintro ⟨⟨_, b⟩, _⟩
    exact Bool.false_ne_true (b.injective (Subsingleton.elim _ _))

def infiniteChart (_ : Unit) : Embedding (complete ℕ) (complete ℕ) :=
  Embedding.id _

theorem infiniteChart_coverage : CoversIrreducibles infiniteChart := by
  intro S _
  exact ⟨(), fun x _ => ⟨x, rfl⟩⟩

def shift : Embedding (complete ℕ) (complete ℕ) where
  toFun := Nat.succ
  injective := Nat.succ_injective
  map_rel_iff := fun _ _ => Iff.rfl

/-- Finiteness is needed for containment to imply equality of B-copies. -/
theorem infinite_actual_copy_not_chart :
    ¬ ∃ i, SameCopy shift (infiniteChart i) := by
  rintro ⟨i, h⟩
  have hz : 0 ∈ copyCarrier shift := by
    rw [h]
    exact ⟨0, rfl⟩
  obtain ⟨n, hn⟩ := hz
  exact Nat.succ_ne_zero n hn

end ACopyChartCoverageRegression

#print axioms StructuralRamsey.Girth.ACopyChartCoverage.factors_through_chart
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.occurrenceCarriers_eq_supportCopies
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.occurrence_quotient_eq_iff
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.occurrenceQuotientEquivSupport
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.occurrenceQuotientEquivSupport_mk
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.actual_copy_eq_chart
#print axioms StructuralRamsey.Girth.ACopyChartCoverage.coversIrreducibles_freeAmalgam
#print axioms ACopyChartCoverageRegression.complete_irreducible
#print axioms ACopyChartCoverageRegression.duplicatedChart_coverage
#print axioms ACopyChartCoverageRegression.duplicate_occurrences_distinct
#print axioms ACopyChartCoverageRegression.duplicate_occurrences_identified
#print axioms ACopyChartCoverageRegression.automorphic_embeddings_distinct
#print axioms ACopyChartCoverageRegression.automorphic_occurrences_identified
#print axioms ACopyChartCoverageRegression.duplicatedChart_exact_support
#print axioms ACopyChartCoverageRegression.finite_actual_copy_is_chart
#print axioms ACopyChartCoverageRegression.singleton_free_amalgam
#print axioms ACopyChartCoverageRegression.singleton_charts_cover_irreducibles
#print axioms ACopyChartCoverageRegression.discrete_pair_not_irreducible
#print axioms ACopyChartCoverageRegression.reducible_copy_missing_from_occurrences
#print axioms ACopyChartCoverageRegression.infiniteChart_coverage
#print axioms ACopyChartCoverageRegression.infinite_actual_copy_not_chart
