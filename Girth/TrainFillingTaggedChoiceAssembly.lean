import Girth.TrainFillingPrivateExtension

set_option Elab.async false

/-!
# Choice-tagged assembly at proper cuts

Different choices share the old target vertices but all private vertices,
edges and proper-cut wagon names are tagged by the choice. The universal
top is intentionally not tagged.

This is the bookkeeping needed after constructing one private first-wagon
extension. It proves that different choice components cannot acquire a
common private vertex or a common proper-cut wagon, and lifts local target
geometry to ComponentTargetGeometry for each tagged component.

No Ramsey arrow, no choice of the uniform witness X, and no universal-top
scattering assertion is made here.
-/

namespace StructuralRamsey.Girth

universe v

structure TaggedChoiceInput (C V Y E P Q : Type v) where
  localCarrier : E → Set (V ⊕ Y)
  localParent : E → P
  properParent : P → Q
  selected : Set E
  selected_inside_old : ∀ e, e ∈ selected →
    localCarrier e ⊆ Set.range (Sum.inl : V → V ⊕ Y)
  local_strong : ∀ e x y,
    x ≠ y →
    Sum.inl x ∈ localCarrier e →
    Sum.inl y ∈ localCarrier e →
    e ∈ selected
  local_cover : ∀ e x,
    Sum.inl x ∈ localCarrier e →
    ∃ f, f ∈ selected ∧
      properParent (localParent f) = properParent (localParent e) ∧
      Sum.inl x ∈ localCarrier f
  local_inter_proper : ∀ e f,
    properParent (localParent e) ≠ properParent (localParent f) →
    ∀ z, z ∈ localCarrier e → z ∈ localCarrier f →
      z ∈ Set.range (Sum.inl : V → V ⊕ Y)

namespace TaggedChoiceInput

variable {C V Y E P Q : Type v} (U : TaggedChoiceInput C V Y E P Q)

abbrev Vertex := V ⊕ (C × Y)
abbrev Edge := C × E
abbrev ProperWagon := C × Q

def placeVertex (c : C) : V ⊕ Y → U.Vertex
  | .inl x => .inl x
  | .inr y => .inr (c, y)

theorem placeVertex_injective (c : C) : Function.Injective (U.placeVertex c) := by
  intro x y h
  cases x <;> cases y <;> simp only [placeVertex, Sum.inl.injEq,
    Sum.inr.injEq, Prod.mk.injEq] at h ⊢ <;> simp_all

@[simp] theorem placeVertex_old (c : C) (x : V) :
    U.placeVertex c (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem placeVertex_private (c : C) (y : Y) :
    U.placeVertex c (Sum.inr y) = Sum.inr (c, y) := rfl

theorem ranges_inter_old (c d : C) (hcd : c ≠ d) :
    Set.range (U.placeVertex c) ∩ Set.range (U.placeVertex d) =
      Set.range (Sum.inl : V → U.Vertex) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    cases z with
    | inl v => exact ⟨v, rfl⟩
    | inr z =>
        cases x with
        | inl v => cases hx
        | inr a =>
          cases y with
          | inl v => cases hy
          | inr b =>
            have hc : c = z.1 := by
              exact congrArg Prod.fst (Sum.inr.inj hx)
            have hd : d = z.1 := by
              exact congrArg Prod.fst (Sum.inr.inj hy)
            exact False.elim (hcd (hc.trans hd.symm))
  · rintro ⟨x, rfl⟩
    exact ⟨⟨Sum.inl x, rfl⟩, ⟨Sum.inl x, rfl⟩⟩

def edgeCarrier (e : U.Edge) : Set U.Vertex :=
  U.placeVertex e.1 '' U.localCarrier e.2

def properParentOf (e : U.Edge) : U.ProperWagon :=
  (e.1, U.properParent (U.localParent e.2))

def topParentOf (_e : U.Edge) : PUnit := PUnit.unit

theorem edgeCarrier_subset_choice (e : U.Edge) :
    U.edgeCarrier e ⊆ Set.range (U.placeVertex e.1) := by
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Distinct choice components may meet only on old target vertices. -/
theorem inter_component_edges_old
    (e f : U.Edge) (hChoice : e.1 ≠ f.1) (z : U.Vertex)
    (he : z ∈ U.edgeCarrier e) (hf : z ∈ U.edgeCarrier f) :
    z ∈ Set.range (Sum.inl : V → U.Vertex) := by
  rw [← U.ranges_inter_old e.1 f.1 hChoice]
  exact ⟨U.edgeCarrier_subset_choice e he, U.edgeCarrier_subset_choice f hf⟩

/-- Proper-cut wagon labels retain the choice tag. -/
theorem properParent_ne_of_choice_ne
    (e f : U.Edge) (hChoice : e.1 ≠ f.1) :
    U.properParentOf e ≠ U.properParentOf f := by
  intro h
  exact hChoice (congrArg Prod.fst h)

/-- The universal top deliberately forgets the choice tag. -/
theorem topParent_eq (e f : U.Edge) :
    U.topParentOf e = U.topParentOf f := rfl

def targetEdges (c : C) : Set U.Edge :=
  {e | e.1 = c ∧ e.2 ∈ U.selected}

noncomputable def data : OrderOneData U.Vertex U.Edge C U.ProperWagon where
  edgeCarrier := U.edgeCarrier
  copyCarrier := fun _ => Set.range (Sum.inl : V → U.Vertex)
  copyEdges := U.targetEdges
  parent := U.properParentOf

theorem target_edge_choice {c : C} {e : U.Edge}
    (he : e ∈ U.targetEdges c) : e.1 = c := he.1

theorem selected_edge_carrier_old {c : C} {e : U.Edge}
    (he : e ∈ U.targetEdges c) :
    U.edgeCarrier e ⊆ Set.range (Sum.inl : V → U.Vertex) := by
  rintro z ⟨w, hw, rfl⟩
  have hOld := U.selected_inside_old e.2 he.2 hw
  obtain ⟨x, hx⟩ := hOld
  subst w
  exact ⟨x, rfl⟩

/-- At every proper cut, each tagged choice component has exactly the
geometry required by the scattering transfer. -/
noncomputable def componentGeometry (c : C) :
    (U.data).ComponentTargetGeometry c where
  componentEdges := {e | e.1 = c}
  inter_wagon_intersections := by
    intro e he f hf hParent z hzE hzF
    have hc : e.1 = c := he
    have hfc : f.1 = c := hf
    have hLocalParent :
        U.properParent (U.localParent e.2) ≠
          U.properParent (U.localParent f.2) := by
      intro h
      apply hParent
      rw [properParentOf, properParentOf, hc, hfc]
      exact congrArg (Prod.mk c) h
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hOld := U.local_inter_proper e.2 f.2 hLocalParent x hx (by
      have hEq : U.placeVertex c x = U.placeVertex c y := by
        simpa only [hc, hfc] using hxz.trans hyz.symm
      have hxy : x = y := U.placeVertex_injective c hEq
      simpa only [hxy] using hy)
    obtain ⟨v, hv⟩ := hOld
    exact ⟨v, by simpa only [hc, placeVertex_old] using hxz.symm.trans (congrArg (U.placeVertex c) hv)⟩
  strong_target := by
    intro e he x y hxy hxE hyE hxT hyT
    have hc : e.1 = c := he
    obtain ⟨x0, hx0⟩ := hxT
    obtain ⟨y0, hy0⟩ := hyT
    have hxLocal : Sum.inl x0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwx⟩ := hxE
      have hPlace : U.placeVertex e.1 w = U.placeVertex e.1 (Sum.inl x0) := by
        simpa only [placeVertex_old] using hwx.trans hx0
      have hwEq : w = Sum.inl x0 := U.placeVertex_injective e.1 hPlace
      simpa only [hwEq] using hw
    have hyLocal : Sum.inl y0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwy⟩ := hyE
      have hPlace : U.placeVertex e.1 w = U.placeVertex e.1 (Sum.inl y0) := by
        simpa only [placeVertex_old] using hwy.trans hy0
      have hwEq : w = Sum.inl y0 := U.placeVertex_injective e.1 hPlace
      simpa only [hwEq] using hw
    have hxy0 : x0 ≠ y0 := by
      intro h
      subst y0
      exact hxy (hx0.symm.trans hy0)
    exact ⟨hc, U.local_strong e.2 x0 y0 hxy0 hxLocal hyLocal⟩
  pointwise_cover := by
    intro e he x hxE hxT
    have hc : e.1 = c := he
    obtain ⟨x0, hx0⟩ := hxT
    have hxLocal : Sum.inl x0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwx⟩ := hxE
      have hPlace : U.placeVertex e.1 w = U.placeVertex e.1 (Sum.inl x0) := by
        simpa only [placeVertex_old] using hwx.trans hx0
      have hwEq : w = Sum.inl x0 := U.placeVertex_injective e.1 hPlace
      simpa only [hwEq] using hw
    obtain ⟨f, hfSel, hfParent, hxf⟩ := U.local_cover e.2 x0 hxLocal
    refine ⟨(c, f), ?_, ?_, ?_⟩
    · exact ⟨rfl, hfSel⟩
    · simp only [data, properParentOf]
      exact congrArg (Prod.mk c) hfParent
    · exact ⟨Sum.inl x0, hxf, by simpa only [placeVertex_old] using hx0⟩

end TaggedChoiceInput
end StructuralRamsey.Girth
