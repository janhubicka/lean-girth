import Girth.ACopyDecoratedStar

open StructuralRamsey.Girth
open ACopyExactStar ACopyLayeredStar

namespace ACopyDecoratedStarRegression

def eqSetoid (α : Type) : Setoid α where
  r := Eq
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def levelEq (n : ℕ) : Setoid Bool where
  r a b := n = 0 → a = b
  iseqv := ⟨fun _ _ => rfl, fun h hn => (h hn).symm,
    fun h₁ h₂ hn => (h₁ hn).trans (h₂ hn)⟩

/-- One shared node and one private source node; they acquire one top parent. -/
def nodes : Diagram Unit Unit (fun _ => Bool) (fun _ => Unit) where
  coreEq := fun _ => eqSetoid Unit
  sourceEq := fun n _ => levelEq n
  alpha := fun _ _ => ()
  beta := fun _ _ => false
  core_nested := by
    intro m n hmn a b h
    exact h
  source_nested := by
    intro m n hmn i a b h hn
    apply h
    omega
  compatible := by
    intro n i s t
    constructor
    · intro _ _
      rfl
    · intro _
      rfl
  core_zero := fun _ _ => Iff.rfl
  source_zero := by
    intro i a b
    change (0 = 0 → a = b) ↔ a = b
    simp

def sharedCoord (a : Bool) : ℕ := if a then 1 else 0
def sourceCoord (e a : Bool) : ℕ := if a then (if e then 2 else 1) else 0

/-- Core edge {0,1}; source edges {0,1} and {0,2}. Every natural-number
record is retained, so records 3 and above are genuinely unsupported. -/
def data : ACopyDecoratedStar.Data nodes Bool ℕ (fun _ => ℕ) (fun _ => Bool) where
  coreEq := eqSetoid ℕ
  sourceEq := fun _ => eqSetoid ℕ
  alpha := fun _ => sharedCoord
  beta := fun _ => sharedCoord
  compatible := fun _ _ _ => Iff.rfl
  coreCoord := fun _ => sharedCoord
  sourceCoord := fun _ => sourceCoord
  core_coord_eq := by
    intro e a b
    change sharedCoord a = sharedCoord b ↔ a = b
    cases a <;> cases b <;> simp [sharedCoord]
  source_coord_eq := by
    intro i e a b
    change sourceCoord e a = sourceCoord e b ↔ a = b
    cases e <;> cases a <;> cases b <;> simp [sourceCoord]
  sharedCoord := fun _ _ a => a
  shared_core := fun _ _ _ => rfl
  shared_source := by
    intro i s a
    cases a <;> rfl

theorem private_node_class : contact nodes 0 () (Quotient.mk _ true) = none := by
  apply (SourceStar.contact_eq_none_iff _ _ _ _ (nodes.compatible 0) () _).mpr
  rintro ⟨s, hs⟩
  have h := Quotient.exact hs
  change 0 = 0 → false = true at h
  cases h rfl

/-- Private wagon labels do not imply point-disjointness from the core. -/
theorem private_wagon_meets_core :
    data.corePoint () false ∈
      data.wagonCarrier 0 (ACopyLayeredStar.sourceMap nodes 0 () (Quotient.mk _ true)) ∩
      data.wagonCarrier 0 (ACopyLayeredStar.coreMap nodes 0 (Quotient.mk _ ())) := by
  constructor
  · rw [data.private_wagonCarrier 0 () _ private_node_class]
    refine ⟨true, false, rfl, ?_⟩
    exact data.sharedPoint_eq () () false
  · apply (data.mem_core_wagonCarrier_iff 0 _ _).mpr
    exact Or.inl ⟨(), false, rfl, rfl⟩

/-- The arbitrary-record API permits a record already equal to a supported
coordinate. It does not make a fresh point for every record. -/
theorem retained_record_can_be_supported :
    data.sourceRecord () 0 = data.sourcePoint () true false := rfl

theorem core_three_unsupported :
    ¬ ∃ e a, data.nodePoint e a = data.coreRecord 3 := by
  rintro ⟨e, a, he⟩
  revert he
  refine Quot.inductionOn e ?_
  intro raw he
  cases raw with
  | inl e =>
      have h := (data.coreRecord_eq_iff _ _).mp he
      change sharedCoord a = 3 at h
      cases a <;> simp [sharedCoord] at h
  | inr t =>
      obtain ⟨s, _, hc⟩ := (data.sourceRecord_eq_coreRecord_iff t.1 _ 3).mp he
      change sharedCoord s = 3 at hc
      cases s <;> simp [sharedCoord] at hc

/-- The supported overlap realization need not cover retained point records. -/
theorem supported_realization_not_surjective : ¬ Function.Surjective data.supportedPoint := by
  intro h
  exact core_three_unsupported ((data.supportedPoint_range_iff _).mp (h (data.coreRecord 3)))

/-- The private child above acquires a core parent, with monotone carrier. -/
theorem private_child_core_parent_carrier :
    data.wagonCarrier 0 (ACopyLayeredStar.sourceMap nodes 0 () (Quotient.mk _ true)) ⊆
      data.wagonCarrier 1 (ACopyLayeredStar.coreMap nodes 1 (Quotient.mk _ ())) := by
  have hparent : parent nodes (Nat.zero_le 1)
      (ACopyLayeredStar.sourceMap nodes 0 () (Quotient.mk _ true)) =
      ACopyLayeredStar.coreMap nodes 1 (Quotient.mk _ ()) := by
    apply (parent_sourceMap_eq_coreMap_iff nodes (Nat.zero_le 1) () _ _).mpr
    apply (SourceStar.contact_eq_some_iff _ _ _ _ (nodes.compatible 1) () _ _).mpr
    refine ⟨(), ?_, rfl⟩
    apply Quotient.sound
    change 1 = 0 → false = true
    omega
  rw [← hparent]
  exact data.wagonCarrier_mono (Nat.zero_le 1) _

/-- Empty source sets give an empty generated top even when universal
relations hold vacuously. Universality alone does not imply inhabitation. -/
def emptyNodes : Diagram Empty Empty (fun _ => Empty) (fun _ => Empty) where
  coreEq := fun _ => eqSetoid Empty
  sourceEq := fun _ _ => eqSetoid Empty
  alpha := fun i => nomatch i
  beta := fun i => nomatch i
  core_nested := by
    intro m n hmn a b h
    exact h
  source_nested := by
    intro m n hmn i a b h
    exact h
  compatible := fun _ i => nomatch i
  core_zero := fun _ _ => Iff.rfl
  source_zero := fun i => nomatch i

theorem empty_top_uninhabited : ¬ Nonempty (Wagon emptyNodes 1) := by
  rintro ⟨w⟩
  refine Quot.inductionOn w ?_
  intro raw
  cases raw with
  | inl e => exact nomatch e
  | inr t => exact nomatch t.1

end ACopyDecoratedStarRegression

#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.coreMap_mk
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceMap_mk
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.coreMap_injective
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceMap_injective
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.coreRecord_eq_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceRecord_eq_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceRecord_eq_coreRecord_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceImage_inter_coreImage
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.distinct_sourceImage_inter
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sharedPoint_eq
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.nodePoint
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.nodePoint_injective
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.output_rel_core_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.output_rel_source_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.coreDiagramEmbedding
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.sourceDiagramEmbedding
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.supportedPoint_injective
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.supportedPoint_range_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.point_has_record
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.mem_core_wagonCarrier_iff
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.core_wagonCarrier
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.private_sourceMap_ne_other
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.private_wagonCarrier
#print axioms StructuralRamsey.Girth.ACopyDecoratedStar.Data.wagonCarrier_mono
#print axioms ACopyDecoratedStarRegression.private_node_class
#print axioms ACopyDecoratedStarRegression.private_wagon_meets_core
#print axioms ACopyDecoratedStarRegression.retained_record_can_be_supported
#print axioms ACopyDecoratedStarRegression.core_three_unsupported
#print axioms ACopyDecoratedStarRegression.supported_realization_not_surjective
#print axioms ACopyDecoratedStarRegression.private_child_core_parent_carrier
#print axioms ACopyDecoratedStarRegression.empty_top_uninhabited
