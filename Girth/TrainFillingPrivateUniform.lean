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
  ⟨fun x => T.star (identify p x),
    fun _ _ h => (identify p).injective (T.star.injective h)⟩

/-- Every chosen W* coordinate has exactly the range of the fixed star map,
independently of the first-wagon label. -/
theorem coordinate_range_eq
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (p : P) :
    Set.range (coordinate T oldCarrier identify p) = Set.range T.star := by
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
  coordinate := coordinate T oldCarrier identify
  templateEdges := T.templateEdges
  selectedEdges := fun _ => selectedEdges T
  selected_inside := by
    intro p a ha
    obtain ⟨e, he⟩ := ha
    rw [he, coordinate_range_eq T oldCarrier identify p]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  local_strong := by
    intro p a x y hxy hx hy hxRange hyRange
    have hxStar : x ∈ Set.range T.star := by
      rw [← coordinate_range_eq T oldCarrier identify p]
      exact hxRange
    have hyStar : y ∈ Set.range T.star := by
      rw [← coordinate_range_eq T oldCarrier identify p]
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
    (toPrivateWagonInput T oldCarrier identify).selectedEdges p =
      selectedEdges T := rfl

/-- Hence the checked private scattering geometry is available immediately
after uniformization, for every parent map on first-wagon labels. -/
noncomputable def componentGeometry
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    {Q : Type v} (parent : P → Q) :
    OrderOneData.ComponentTargetGeometry
      ((toPrivateWagonInput T oldCarrier identify).data parent) PUnit.unit :=
  PrivateWagonInput.componentGeometry
    (toPrivateWagonInput T oldCarrier identify) parent

end UniformPrivateTemplate

namespace UniformPrivateTemplate

open StructuralRamsey.RelStructure

universe u
variable {L : RelLanguage.{u}} {UA W X : Type v}

/-- Images of intrinsic support edges commute literally with composition. -/
theorem image_copyCarrier_comp
    (A : RelStructure L UA) (B : RelStructure L W) (R : RelStructure L X)
    (b : Embedding B R) (a : Embedding A B) :
    b.toFunctionEmbedding '' copyCarrier a = copyCarrier (b.comp a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨a z, ⟨z, rfl⟩, rfl⟩

/-- A single A-strong, support-covered relational copy B -> R supplies the
uniform hypergraph template used by the private first-wagon construction. -/
noncomputable def ofStrongEmbedding
    (A : RelStructure L UA) (B : RelStructure L W) (R : RelStructure L X)
    (b : Embedding B R)
    (hStrong : AStrong A R (copyCarrier b))
    (hCovered : ∀ x : W, ∃ a : Embedding A B, x ∈ copyCarrier a) :
    UniformPrivateTemplate W X where
  localEdges := supportCopies A B
  templateEdges := supportCopies A R
  star := b.toFunctionEmbedding
  map_edge := by
    intro e
    obtain ⟨a, ha⟩ := e.2
    refine ⟨b.comp a, ?_⟩
    rw [ha]
    exact image_copyCarrier_comp A B R b a
  strong := by
    intro edge x y hxy hx hy hxRange hyRange
    obtain ⟨a, ha⟩ := edge.2
    have hxA : x ∈ copyCarrier a := by
      rw [← ha]
      exact hx
    have hyA : y ∈ copyCarrier a := by
      rw [← ha]
      exact hy
    change x ∈ copyCarrier b at hxRange
    change y ∈ copyCarrier b at hyRange
    have hMeet : ¬ (copyCarrier a ∩ copyCarrier b).Subsingleton := by
      intro hSmall
      exact hxy (hSmall ⟨hxA, hxRange⟩ ⟨hyA, hyRange⟩)
    have hSub : copyCarrier a ⊆ copyCarrier b := hStrong a hMeet
    have hFactor : ∀ u : UA, ∃ w : W, a u = b w := by
      intro u
      obtain ⟨w, hw⟩ := hSub ⟨u, rfl⟩
      exact ⟨w, hw.symm⟩
    let q : Embedding A B := a.factorThroughRange b hFactor
    have hComp : b.comp q = a := by
      apply Embedding.ext
      intro u
      have hq : a u = b (q u) := Classical.choose_spec (hFactor u)
      exact hq.symm
    let e : {e : Set W // e ∈ supportCopies A B} :=
      ⟨copyCarrier q, ⟨q, rfl⟩⟩
    refine ⟨e, ?_⟩
    calc
      edge.1 = copyCarrier a := ha
      _ = copyCarrier (b.comp q) := congrArg copyCarrier hComp.symm
      _ = b.toFunctionEmbedding '' copyCarrier q :=
        (image_copyCarrier_comp A B R b q).symm
  local_cover := by
    intro x
    obtain ⟨a, hx⟩ := hCovered x
    exact ⟨⟨copyCarrier a, ⟨a, rfl⟩⟩, hx⟩

end UniformPrivateTemplate

end StructuralRamsey.Girth
