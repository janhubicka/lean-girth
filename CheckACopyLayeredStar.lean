import Girth.ACopyLayeredStar

open StructuralRamsey.Girth
open ACopyExactStar ACopyLayeredStar

#check generated_zero_iff_shared
#check generated_nested
#check generated_iff_normal
#check nodeSetoid_mk_iff
#check nodeSetoid_source_iff
#check parent_sourceMap
#check contact_parent
#check parent_sourceMap_eq_coreMap_iff
#check nodeWagonEquiv
#check generated_top
#check uniqueTop

namespace ACopyLayeredStarRegression

/-- The zero cut is equality; every positive cut has one source class. -/
def levelEq (n : ℕ) : Setoid Bool where
  r a b := n = 0 → a = b
  iseqv := ⟨fun _ _ => rfl, fun h hn => (h hn).symm,
    fun h₁ h₂ hn => (h₁ hn).trans (h₂ hn)⟩

theorem level_nested {m n : ℕ} (hmn : m ≤ n) {a b : Bool}
    (h : levelEq m a b) : levelEq n a b := by
  intro hn
  apply h
  omega

/-- Each of two Boolean source node sets shares only its `false` node. -/
def diagram : Diagram Bool Bool (fun _ => Bool) (fun _ => Unit) where
  coreEq := levelEq
  sourceEq := fun n _ => levelEq n
  alpha := fun _ _ => false
  beta := fun _ _ => false
  core_nested := by
    intro m n hmn a b h
    exact level_nested hmn h
  source_nested := by
    intro m n hmn i a b h
    exact level_nested hmn h
  compatible := fun _ _ _ _ => Iff.rfl
  core_zero := by
    intro a b
    change (0 = 0 → a = b) ↔ a = b
    simp
  source_zero := by
    intro i a b
    change (0 = 0 → a = b) ↔ a = b
    simp

theorem child_private :
    contact diagram 0 false (Quotient.mk _ true) = none := by
  apply (SourceStar.contact_eq_none_iff _ _ _ _ (diagram.compatible 0) false _).mpr
  rintro ⟨s, hs⟩
  have h := Quotient.exact hs
  change 0 = 0 → false = true at h
  cases h rfl

theorem parent_contacts :
    contact diagram 1 false
      (sourceParent diagram (Nat.zero_le 1) false (Quotient.mk _ true)) =
      some (coreParent diagram (Nat.zero_le 1) (Quotient.mk _ false)) := by
  apply (SourceStar.contact_eq_some_iff _ _ _ _ (diagram.compatible 1) false _ _).mpr
  refine ⟨(), ?_, rfl⟩
  apply Quotient.sound
  change 1 = 0 → false = true
  omega

/-- A genuine private child acquires a core parent in the generated quotient. -/
theorem private_child_core_parent :
    contact diagram 0 false (Quotient.mk _ true) = none ∧
    parent diagram (Nat.zero_le 1)
      (sourceMap diagram 0 false (Quotient.mk _ true)) =
      coreMap diagram 1 (coreParent diagram (Nat.zero_le 1) (Quotient.mk _ false)) := by
  refine ⟨child_private, ?_⟩
  exact (parent_sourceMap_eq_coreMap_iff diagram (Nat.zero_le 1) false _ _).mpr
    parent_contacts

/-- The same child really has no core image at level zero. -/
theorem child_not_core (c : Quotient (diagram.coreEq 0)) :
    sourceMap diagram 0 false (Quotient.mk _ true) ≠ coreMap diagram 0 c := by
  intro h
  have hc := (sourceMap_eq_coreMap_iff diagram 0 false _ c).mp h
  rw [child_private] at hc
  cases hc

/-- Both original source nodes embed distinctly into the actual node pushout. -/
theorem basic_nodes_distinct : nodeSource diagram false false ≠ nodeSource diagram false true := by
  intro h
  exact Bool.false_ne_true (nodeSource_injective diagram false h)

/-- They become equivalent only at the generated higher cut. -/
theorem merge_at_parent :
    ¬ nodeSetoid diagram 0 (nodeSource diagram false false) (nodeSource diagram false true) ∧
    nodeSetoid diagram 1 (nodeSource diagram false false) (nodeSource diagram false true) := by
  constructor
  · rw [nodeSetoid_zero]
    exact basic_nodes_distinct
  · rw [nodeSetoid_source_iff]
    change 1 = 0 → false = true
    omega

theorem top_universal (x y : Node diagram) : nodeSetoid diagram 1 x y := by
  apply nodeSetoid_top diagram 1
  · intro _ _
    change 1 = 0 → _
    omega
  · intro _ _ _
    change 1 = 0 → _
    omega
  · intro _
    exact ⟨()⟩

end ACopyLayeredStarRegression

#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_zero_iff_shared
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.step_nested
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_nested
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_core_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_source_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_iff_normal
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_mk
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_refl
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_comp
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_surjective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.coreParent
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.sourceParent
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.coreMap
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.sourceMap
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.coreMap_injective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.sourceMap_injective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_coreMap
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_sourceMap
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.contact_parent
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.sourceMap_eq_coreMap_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.parent_sourceMap_eq_coreMap_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeCore
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSource
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeCore_injective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSource_injective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_mk_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_nested
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_zero
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_core_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_source_iff
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeWagonMap
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeWagonMap_bijective
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeWagonEquiv
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.top_source_core
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.generated_top
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.top_subsingleton
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.nodeSetoid_top
#print axioms StructuralRamsey.Girth.ACopyLayeredStar.uniqueTop
#print axioms ACopyLayeredStarRegression.levelEq
#print axioms ACopyLayeredStarRegression.level_nested
#print axioms ACopyLayeredStarRegression.diagram
#print axioms ACopyLayeredStarRegression.child_private
#print axioms ACopyLayeredStarRegression.parent_contacts
#print axioms ACopyLayeredStarRegression.private_child_core_parent
#print axioms ACopyLayeredStarRegression.child_not_core
#print axioms ACopyLayeredStarRegression.basic_nodes_distinct
#print axioms ACopyLayeredStarRegression.merge_at_parent
#print axioms ACopyLayeredStarRegression.top_universal
