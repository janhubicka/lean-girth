import Girth.TrainFillingPrivateExtension

set_option Elab.async false

/-!
# Heterogeneous choice-indexed first-wagon extensions

Unlike the constant-choice interface, each choice c may have a DIFFERENT
PrivateWagonInput U c. The dependent sums retain its own vertices, edges,
chosen strong copy, and private coordinates. This is the correct shape for
the family indexed by all embeddings W* of W into the Ramsey template X.

Proper-cut wagon names carry the choice tag; the common universal top does
not. No choice of X or Ramsey arrow is asserted by this bookkeeping module.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q : Type v}
variable (U : C → PrivateWagonInput V P X)

abbrev Vertex (U : C → PrivateWagonInput V P X) :=
  Sigma (fun c : C => (U c).Vertex)
abbrev Edge (U : C → PrivateWagonInput V P X) :=
  Sigma (fun c : C => (U c).Edge)
abbrev ProperWagon (_U : C → PrivateWagonInput V P X) := C × Q

def tagVertex (c : C) (z : (U c).Vertex) : Vertex U := ⟨c, z⟩
def tagEdge (c : C) (e : (U c).Edge) : Edge U := ⟨c, e⟩

theorem tagVertex_injective (c : C) :
    Function.Injective (tagVertex U c) := by
  intro x y h
  cases h
  rfl

theorem tagEdge_injective (c : C) :
    Function.Injective (tagEdge U c) := by
  intro x y h
  cases h
  rfl

def componentCarrier (c : C) : Set (Vertex U) :=
  Set.range (tagVertex U c)
def componentEdges (c : C) : Set (Edge U) :=
  Set.range (tagEdge U c)

def edgeCarrier (e : Edge U) : Set (Vertex U) :=
  (tagVertex U e.1) '' (U e.1).edgeCarrier e.2

theorem edgeCarrier_subset_component (e : Edge U) :
    edgeCarrier U e ⊆ componentCarrier U e.1 := by
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Different choices are fully vertex-disjoint, even on original target
vertices. First wagons inside one fixed choice may still intersect. -/
theorem componentCarrier_disjoint (c d : C) (h : c ≠ d) :
    Disjoint (componentCarrier U c) (componentCarrier U d) := by
  rw [Set.disjoint_left]
  intro z hzC hzD
  obtain ⟨x, hx⟩ := hzC
  obtain ⟨y, hy⟩ := hzD
  exact h (congrArg Sigma.fst (hx.trans hy.symm))

theorem edge_carriers_disjoint_of_choice_ne
    (e f : Edge U) (h : e.1 ≠ f.1) :
    Disjoint (edgeCarrier U e) (edgeCarrier U f) := by
  rw [Set.disjoint_left]
  intro z he hf
  exact (Set.disjoint_left.mp (componentCarrier_disjoint U e.1 f.1 h))
    (edgeCarrier_subset_component U e he)
    (edgeCarrier_subset_component U f hf)

def properParentOf (parent : P → Q) (e : Edge U) :
    ProperWagon (Q := Q) U :=
  (e.1, parent e.2.1)

theorem properParent_ne_of_choice_ne
    (parent : P → Q) (e f : Edge U) (h : e.1 ≠ f.1) :
    properParentOf U parent e ≠ properParentOf U parent f := by
  intro hp
  exact h (congrArg Prod.fst hp)

/-- Only the universal top identifies wagon names across choices. -/
def topParentOf (_e : Edge U) : PUnit := PUnit.unit

theorem topParent_eq (e f : Edge U) :
    topParentOf U e = topParentOf U f := rfl

def targetCarrier (c : C) : Set (Vertex U) :=
  (tagVertex U c) '' Set.range
    (Sum.inl : V → (U c).Vertex)

def targetEdges (c : C) : Set (Edge U) :=
  (tagEdge U c) '' (U c).targetEdges

theorem targetCarrier_subset_component (c : C) :
    targetCarrier U c ⊆ componentCarrier U c := by
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

theorem targetEdges_subset_component (c : C) :
    targetEdges U c ⊆ componentEdges U c := by
  rintro e ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Local strong selected edges stay within the target of their own
choice; target copies from different choices remain disjoint. -/
theorem target_edge_carrier_subset
    (c : C) (e : Edge U) (he : e ∈ targetEdges U c) :
    edgeCarrier U e ⊆ targetCarrier U c := by
  obtain ⟨f, hf, rfl⟩ := he
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, (U c).selected_carrier_old f hf hx, rfl⟩

end StructuralRamsey.Girth.IndexedPrivateChoice
