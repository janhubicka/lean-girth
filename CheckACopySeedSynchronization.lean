import Girth.ACopySeedSynchronization

open StructuralRamsey.Girth.ACopySeedSynchronization

/-! A finite regression against replacing synchronization by chart lifting.
The three two-element base members have the two-colour Ramsey property.
Each is lifted to its own disjoint pair, with an exact, injective projection;
the lifted family is not Ramsey.  No geometric cover theorem is asserted. -/
namespace ACopySeedSynchronizationRegression

def base (b : Fin 3) : Set (Fin 3) := {x | x ≠ b}

def lifted (b : Fin 3) : Set (Fin 3 × Bool) := {y | y.1 = b}

def project (y : Fin 3 × Bool) : Fin 3 :=
  if y.2 then (if y.1 = 2 then 1 else 2) else (if y.1 = 0 then 1 else 0)

theorem base_arrow : FamilyArrow base Bool := by
  unfold FamilyArrow base
  decide

theorem projection_exact (b : Fin 3) : project '' lifted b = base b := by
  ext x
  change (∃ y : Fin 3 × Bool, y.1 = b ∧ project y = x) ↔ x ≠ b
  fin_cases b <;> fin_cases x <;> decide

theorem projection_injective (b : Fin 3) : Set.InjOn project (lifted b) := by
  intro x hx y hy hxy
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, c⟩
  change i = b at hx
  change j = b at hy
  subst i
  subst j
  fin_cases b <;> cases a <;> cases c <;> simp_all [project]

theorem projection_respects : Projects base lifted id project := by
  intro b y hy
  change project y ∈ base b
  rw [← projection_exact b]
  exact ⟨y, hy, rfl⟩

theorem every_chart_lifts (b : Fin 3) :
    ∃ j, id j = b ∧ project '' lifted j = base b :=
  ⟨b, rfl, projection_exact b⟩

theorem lifted_disjoint {b c : Fin 3} (hbc : b ≠ c) :
    Disjoint (lifted b) (lifted c) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  exact hbc (hy.symm.trans hz)

theorem lifted_cover (y : Fin 3 × Bool) : ∃ b, y ∈ lifted b :=
  ⟨y.1, rfl⟩

theorem lifted_not_arrow : ¬ FamilyArrow lifted Bool := by
  intro h
  obtain ⟨b, k, hb⟩ := h Prod.snd
  have hfalse := hb (b, false) rfl
  have htrue := hb (b, true) rfl
  exact Bool.false_ne_true (hfalse.trans htrue.symm)

theorem not_synchronized : ¬ Synchronizes lifted id project Bool := by
  intro h
  exact lifted_not_arrow (familyArrow_of_synchronizes projection_respects h base_arrow)

/-- Unused seed nodes do not prevent extension of a fibre-constant colouring. -/
theorem empty_fibre_extension (χ : Unit → Bool) :
    ∃ c : Bool → Bool, ∀ x : Unit, χ x = c false :=
  factor_through_of_fibreConstant (fun _ : Unit => false) χ
    (fun x y _ => congrArg χ (Subsingleton.elim x y))

end ACopySeedSynchronizationRegression

#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.familyArrow_of_synchronizes
#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.factor_through_of_fibreConstant
#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.backwardFusion
#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.factorization_of_finitePass
#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.synchronizes_of_factorizingSelections
#print axioms StructuralRamsey.Girth.ACopySeedSynchronization.synchronizes_of_finitePass
#print axioms ACopySeedSynchronizationRegression.base_arrow
#print axioms ACopySeedSynchronizationRegression.projection_exact
#print axioms ACopySeedSynchronizationRegression.projection_injective
#print axioms ACopySeedSynchronizationRegression.projection_respects
#print axioms ACopySeedSynchronizationRegression.every_chart_lifts
#print axioms ACopySeedSynchronizationRegression.lifted_disjoint
#print axioms ACopySeedSynchronizationRegression.lifted_cover
#print axioms ACopySeedSynchronizationRegression.lifted_not_arrow
#print axioms ACopySeedSynchronizationRegression.not_synchronized
#print axioms ACopySeedSynchronizationRegression.empty_fibre_extension
