import Girth.TrainFillingPrivateExtension

set_option Elab.async false

/-!
# Uniform local templates instantiate the private scattering input

Section 16 first makes every first wagon a copy of one finite template W,
then chooses one strong copy W* inside a common Ramsey template X.  The
private-extension construction only needs the resulting coordinate maps,
the local support edges, strongness of W* inside X and pointwise coverage.

This file packages that manuscript step.  It does not choose the Ramsey
template X, prove its arrow, assemble the disjoint choice components, or
perform the final filling.
-/

namespace StructuralRamsey.Girth

universe v

/-- One strong, covered copy of a uniform local edge template W inside X. -/
structure UniformPrivateTemplate (W X : Type v) where
  localEdges : Set (Set W)
  templateEdges : Set (Set X)
  star : W ↪ X
  map_edge : ∀ e : {e : Set W // e ∈ localEdges},
    star '' e.1 ∈ templateEdges
  strong : ∀ (a : {a : Set X // a ∈ templateEdges}) x y,
    x ≠ y → x ∈ a.1 → y ∈ a.1 →
    x ∈ Set.range star → y ∈ Set.range star →
    ∃ e : {e : Set W // e ∈ localEdges}, a.1 = star '' e.1
  local_cover : ∀ x : W,
    ∃ e : {e : Set W // e ∈ localEdges}, x ∈ e.1

namespace UniformPrivateTemplate

variable {V P W X : Type v} (T : UniformPrivateTemplate W X)

/-- The actual template edges belonging to the chosen copy W* in X. -/
def selectedEdges : Set {a : Set X // a ∈ T.templateEdges} :=
  {a | ∃ e : {e : Set W // e ∈ T.localEdges}, a.1 = T.star '' e.1}

/-- Compose the old first-wagon identification with the chosen W* embedding. -/
def coordinate
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (p : P) : {x : V // x ∈ oldCarrier p} ↪ X :=
  T.star.comp (identify p).toEmbedding

/-- Every chosen W* coordinate has exactly the range of the fixed star map,
independently of the first-wagon label. -/
theorem coordinate_range_eq
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (p : P) :
    Set.range (T.coordinate oldCarrier identify p) = Set.range T.star := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨identify p z, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(identify p).symm w, ?_⟩
    change T.star (identify p ((identify p).symm w)) = T.star w
    rw [Equiv.apply_symm_apply]

/-- A uniformized first-wagon family and one strong covered copy W*⊂X
automatically supply every field of PrivateWagonInput. -/
noncomputable def toPrivateWagonInput
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W) :
    PrivateWagonInput V P X where
  oldCarrier := oldCarrier
  coordinate := T.coordinate oldCarrier identify
  templateEdges := T.templateEdges
  selectedEdges := fun _ => T.selectedEdges
  selected_inside := by
    intro p a ha
    obtain ⟨e, he⟩ := ha
    rw [he, T.coordinate_range_eq oldCarrier identify p]
    exact Set.image_subset_range
  local_strong := by
    intro p a x y hxy hx hy hxRange hyRange
    have hxStar : x ∈ Set.range T.star := by
      rw [← T.coordinate_range_eq oldCarrier identify p]
      exact hxRange
    have hyStar : y ∈ Set.range T.star := by
      rw [← T.coordinate_range_eq oldCarrier identify p]
      exact hyRange
    obtain ⟨e, he⟩ := T.strong a x y hxy hx hy hxStar hyStar
    exact ⟨e, he⟩
  local_cover := by
    intro p x
    obtain ⟨e, hxe⟩ := T.local_cover (identify p x)
    let a : {a : Set X // a ∈ T.templateEdges} :=
      ⟨T.star '' e.1, T.map_edge e⟩
    refine ⟨a, ?_, ?_⟩
    · exact ⟨e, rfl⟩
    · exact ⟨identify p x, hxe, rfl⟩

/-- The selected local edges in every first wagon are the same labelled W*
edge family; the wagon label affects only which old vertices are identified. -/
@[simp] theorem toPrivateWagonInput_selectedEdges
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (p : P) :
    (T.toPrivateWagonInput oldCarrier identify).selectedEdges p =
      T.selectedEdges := rfl

/-- Hence the checked private scattering geometry is available immediately
after uniformization, for every parent map on first-wagon labels. -/
noncomputable def componentGeometry
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    {Q : Type v} (parent : P → Q) :
    ((T.toPrivateWagonInput oldCarrier identify).data parent).
      ComponentTargetGeometry PUnit.unit :=
  (T.toPrivateWagonInput oldCarrier identify).componentGeometry parent

end UniformPrivateTemplate
end StructuralRamsey.Girth
