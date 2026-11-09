import Girth.ACopyExactStar

open StructuralRamsey.Girth.ACopyExactStar

#check SourceStar.generated_iff_normal
#check SourceStar.generated_core_iff
#check SourceStar.generated_source_iff
#check SourceStar.generated_source_core_iff
#check SourceStar.core_classMap_injective
#check SourceStar.source_classMap_injective
#check SourceStar.generated_distinct_sources_iff
#check SourceStar.quotientEquiv
#check ClassStar.normal_range_iff
#check SourceStar.private_label_range_iff

namespace ACopyExactStarRegression

/-- A source equivalence with genuinely different representatives. -/
def parity : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def oldEq : Bool → Setoid ℕ := fun _ => parity
def sharedCore : Bool → Unit → ℕ := fun _ _ => 1
def sharedOld : Bool → Unit → ℕ := fun _ _ => 0

theorem compatible : ∀ i s t,
    parity (sharedCore i s) (sharedCore i t) ↔
      oldEq i (sharedOld i s) (sharedOld i t) := by
  intro i s t
  simp [sharedCore, sharedOld]

/-- Source 2 is joined through shared 0 to core 1, then core 3. -/
theorem transitive_source_core :
    SourceStar.Generated parity oldEq sharedCore sharedOld
      (.inr ⟨false, 2⟩) (.inl 3) := by
  apply (SourceStar.generated_source_core_iff parity oldEq sharedCore sharedOld
    compatible false 2 3).mpr
  exact ⟨(), rfl, rfl⟩

/-- Distinct source representatives meet via their common core class. -/
theorem transitive_cross_source :
    SourceStar.Generated parity oldEq sharedCore sharedOld
      (.inr ⟨false, 2⟩) (.inr ⟨true, 4⟩) := by
  apply (SourceStar.generated_distinct_sources_iff parity oldEq sharedCore sharedOld
    compatible false true (by decide) 2 4).mpr
  refine ⟨3, transitive_source_core, ?_⟩
  apply (SourceStar.generated_source_core_iff parity oldEq sharedCore sharedOld
    compatible true 4 3).mpr
  exact ⟨(), rfl, rfl⟩

/-- The two parity classes of a source do not collapse. -/
theorem no_source_fold :
    ¬ SourceStar.Generated parity oldEq sharedCore sharedOld
      (.inr ⟨false, 2⟩) (.inr ⟨false, 1⟩) := by
  rw [SourceStar.generated_source_iff parity oldEq sharedCore sharedOld compatible]
  change ¬ ((2 : ℕ) % 2 = 1 % 2)
  decide

/-- Noncontacting odd classes retain separate source indices. -/
theorem private_sources_separate :
    ¬ SourceStar.Generated parity oldEq sharedCore sharedOld
      (.inr ⟨false, 1⟩) (.inr ⟨true, 1⟩) := by
  intro h
  obtain ⟨c, hc, _⟩ :=
    (SourceStar.generated_distinct_sources_iff parity oldEq sharedCore sharedOld
      compatible false true (by decide) 1 1).mp h
  obtain ⟨s, hs, _⟩ :=
    (SourceStar.generated_source_core_iff parity oldEq sharedCore sharedOld
      compatible false 1 c).mp hc
  have hFalse : ¬ oldEq false (sharedOld false s) 1 := by
    change ¬ ((0 : ℕ) % 2 = 1 % 2)
    decide
  exact hFalse hs

end ACopyExactStarRegression

#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_normal
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_iff_normal
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_core_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_source_core_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_source_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.generated_distinct_sources_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.normal_range_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.quotientNormal
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.quotientNormal_bijective
#print axioms StructuralRamsey.Girth.ACopyExactStar.ClassStar.quotientEquiv
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.touch_unique
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.touch_injective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.contact
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.contact_eq_some_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.contact_injective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.contact_eq_none_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.private_label_range_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.classToQuotient
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.classToQuotient_classes
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.classToQuotient_contact
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_iff_class_generated
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_iff_normal
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_core_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_source_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_source_core_iff
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.core_classMap_injective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.source_classMap_injective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.classes_surjective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.quotientNormal
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.quotientNormal_bijective
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.quotientEquiv
#print axioms StructuralRamsey.Girth.ACopyExactStar.SourceStar.generated_distinct_sources_iff
#print axioms ACopyExactStarRegression.compatible
#print axioms ACopyExactStarRegression.transitive_source_core
#print axioms ACopyExactStarRegression.transitive_cross_source
#print axioms ACopyExactStarRegression.no_source_fold
#print axioms ACopyExactStarRegression.private_sources_separate
