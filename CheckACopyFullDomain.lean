import Girth.ACopyFullDomain

open StructuralRamsey.Girth
open StructuralRamsey.Girth.ACopyExactStar
open StructuralRamsey.Girth.ACopyLayeredStar
open StructuralRamsey.Girth.ACopyDecoratedStar
open StructuralRamsey.Girth.ACopyFullDomain

namespace ACopyFullDomainRegression

/-- Three edges form the path 0--1--2--3. -/
def coord (e : Fin 3) (a : Bool) : Fin 4 :=
  ⟨e.val + if a then 1 else 0, by have := e.isLt; cases a <;> simp_all <;> omega⟩

theorem coord_eq_iff (e : Fin 3) (a b : Bool) : coord e a = coord e b ↔ a = b := by
  fin_cases e <;> cases a <;> cases b <;> decide

theorem path_linear : ∀ e f : Fin 3, e ≠ f →
    (Set.range (coord e) ∩ Set.range (coord f)).Subsingleton := by decide

def nodes {Q : Type} (glue : Q → Fin 3) :
    Diagram (Fin 3) Unit (fun _ => Fin 3) (fun _ => Q) where
  coreEq := fun _ => ⊥
  sourceEq := fun _ _ => ⊥
  alpha := fun _ => glue
  beta := fun _ => glue
  core_nested := by intro m n hmn a b h; exact h
  source_nested := by intro m n hmn i a b h; exact h
  compatible := fun _ _ _ _ => Iff.rfl
  core_zero := fun _ _ => Iff.rfl
  source_zero := fun _ _ _ => Iff.rfl

/-- The full four-point domain is shared; the parameter chooses only the
node labels that are explicitly identified. -/
def points {Q : Type} (glue : Q → Fin 3) :
    Data (nodes glue) Bool (Fin 4) (fun _ => Fin 4) (fun _ => Fin 4) where
  coreEq := ⊥
  sourceEq := fun _ => ⊥
  alpha := fun _ p => p
  beta := fun _ p => p
  compatible := fun _ _ _ => Iff.rfl
  coreCoord := coord
  sourceCoord := fun _ => coord
  core_coord_eq := coord_eq_iff
  source_coord_eq := fun _ => coord_eq_iff
  sharedCoord := fun _ q => coord (glue q)
  shared_core := fun _ _ _ => rfl
  shared_source := fun _ _ _ => rfl

theorem local_core_faithful {Q : Type} (glue : Q → Fin 3) :
    Function.Injective (coreNodeCarrier (points glue)) := by
  intro e f h
  obtain ⟨a, ha⟩ := h ▸ (show Quotient.mk (points glue).coreEq (coord e false) ∈
    coreNodeCarrier (points glue) e from ⟨false, rfl⟩)
  obtain ⟨b, hb⟩ := h.symm ▸ (show Quotient.mk (points glue).coreEq (coord f false) ∈
    coreNodeCarrier (points glue) f from ⟨false, rfl⟩)
  have hva := congrArg Fin.val (show coord f a = coord e false from Quotient.exact ha)
  have hvb := congrArg Fin.val (show coord e b = coord f false from Quotient.exact hb)
  have hfe : f.val ≤ e.val := by cases a <;> simp [coord] at hva <;> omega
  have hef : e.val ≤ f.val := by cases b <;> simp [coord] at hvb <;> omega
  apply Fin.ext
  omega

theorem local_source_faithful {Q : Type} (glue : Q → Fin 3) (i : Unit) :
    Function.Injective (sourceNodeCarrier (points glue) i) :=
  local_core_faithful glue

def outer : Bool → Fin 3 := fun q => if q then 2 else 0

/-- Every shared point is covered by an explicitly shared OUTER node.
Thus point coverage alone cannot replace fullness of the node domain. -/
theorem outer_nodes_cover_all_points :
    ∀ p : Fin 4, ∃ q : Bool, ∃ a : Bool, coord (outer q) a = p := by decide

theorem middle_nodes_distinct :
    nodeSource (nodes outer) () 1 ≠ nodeCore (nodes outer) 1 := by
  intro h
  obtain ⟨q, hq, _⟩ :=
    (SourceStar.generated_source_core_iff ((nodes outer).coreEq 0)
      ((nodes outer).sourceEq 0) (nodes outer).alpha (nodes outer).beta
      ((nodes outer).compatible 0) () (1 : Fin 3) (1 : Fin 3)).mp
        (Quot.eqvGen_exact h)
  change outer q = (1 : Fin 3) at hq
  cases q <;> contradiction

/-- The omitted middle nodes nevertheless have exactly the same two-point
carrier in the genuinely generated decorated quotient. -/
theorem middle_carriers_equal :
    nodeCarrier (points outer) (nodeSource (nodes outer) () 1) =
      nodeCarrier (points outer) (nodeCore (nodes outer) 1) := by
  have hPoint (a : Bool) :
      (points outer).sourcePoint () 1 a = (points outer).corePoint 1 a :=
    Quot.sound (SourceStar.Step.shared
      (coreEq := (points outer).coreEq) (sourceEq := (points outer).sourceEq)
      (alpha := (points outer).alpha) (beta := (points outer).beta) () (coord 1 a))
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hPoint a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, hPoint a⟩

theorem outer_domain_not_full : ¬ FullNodeDomains (points outer) := by
  intro h
  obtain ⟨q, hq⟩ := h () 1 (by
    rintro p ⟨a, rfl⟩
    exact ⟨coord 1 a, rfl⟩)
  change outer q = (1 : Fin 3) at hq
  cases q <;> contradiction

theorem point_coverage_insufficient :
    ¬ Function.Injective (nodeCarrier (points outer)) := by
  intro h
  exact middle_nodes_distinct (h middle_carriers_equal)

/-- Sharing the complete induced node domain repairs precisely the missing
condition, without adding a hypothesis about output carriers. -/
theorem complete_domain_full : FullNodeDomains (points (id : Fin 3 → Fin 3)) := by
  intro _ e _
  exact ⟨e, rfl⟩

theorem complete_domain_faithful :
    Function.Injective (nodeCarrier (points (id : Fin 3 → Fin 3))) :=
  nodeCarrier_injective _ (local_core_faithful id)
    (local_source_faithful id) complete_domain_full

end ACopyFullDomainRegression

#print axioms StructuralRamsey.Girth.ACopyFullDomain.nodeCarrier_core_subset
#print axioms StructuralRamsey.Girth.ACopyFullDomain.nodeCarrier_source_subset
#print axioms StructuralRamsey.Girth.ACopyFullDomain.core_carrier_eq_iff
#print axioms StructuralRamsey.Girth.ACopyFullDomain.source_carrier_eq_iff
#print axioms StructuralRamsey.Girth.ACopyFullDomain.source_node_shared_of_subset_core
#print axioms StructuralRamsey.Girth.ACopyFullDomain.source_node_eq_core_of_carrier_eq
#print axioms StructuralRamsey.Girth.ACopyFullDomain.nodeCarrier_injective
#print axioms StructuralRamsey.Girth.ACopyFullDomain.nodeCarrier_eq_iff
#print axioms ACopyFullDomainRegression.coord_eq_iff
#print axioms ACopyFullDomainRegression.path_linear
#print axioms ACopyFullDomainRegression.local_core_faithful
#print axioms ACopyFullDomainRegression.local_source_faithful
#print axioms ACopyFullDomainRegression.outer_nodes_cover_all_points
#print axioms ACopyFullDomainRegression.middle_nodes_distinct
#print axioms ACopyFullDomainRegression.middle_carriers_equal
#print axioms ACopyFullDomainRegression.outer_domain_not_full
#print axioms ACopyFullDomainRegression.point_coverage_insufficient
#print axioms ACopyFullDomainRegression.complete_domain_full
#print axioms ACopyFullDomainRegression.complete_domain_faithful
