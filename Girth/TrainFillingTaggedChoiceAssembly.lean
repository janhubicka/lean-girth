import Girth.TrainFillingPrivateExtension
import Girth.TrainDesignatedSubcopyGirth

set_option Elab.async false

/-!
# Choice-tagged assembly at proper cuts

A single private first-wagon extension may share its OLD target vertices
between first wagons. Different CHOICES in G0, however, are disjoint copies.
Accordingly every vertex, edge, target label and proper-cut wagon name carries
the choice tag. The universal top alone is intentionally untagged.

The file constructs the proper-cut component geometry from local component
geometry. It does not choose the uniform Ramsey witness X, identify the final
target train, prove the Ramsey arrow, or invoke scattering at the universal top.
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

abbrev LocalVertex (_U : TaggedChoiceInput C V Y E P Q) := V ⊕ Y
abbrev Vertex (U : TaggedChoiceInput C V Y E P Q) := C × U.LocalVertex
abbrev Edge (_U : TaggedChoiceInput C V Y E P Q) := C × E
abbrev ProperWagon (_U : TaggedChoiceInput C V Y E P Q) := C × Q

def placeVertex (c : C) (z : U.LocalVertex) : U.Vertex := (c, z)

theorem placeVertex_injective (c : C) : Function.Injective (U.placeVertex c) := by
  intro x y h
  exact congrArg Prod.snd h

@[simp] theorem placeVertex_old (c : C) (x : V) :
    U.placeVertex c (Sum.inl x) = (c, Sum.inl x) := rfl

def edgeCarrier (e : U.Edge) : Set U.Vertex :=
  U.placeVertex e.1 '' U.localCarrier e.2

def componentCarrier (c : C) : Set U.Vertex :=
  Set.range (U.placeVertex c)

def componentEdges (c : C) : Set U.Edge :=
  {e | e.1 = c}

def properParentOf (e : U.Edge) : U.ProperWagon :=
  (e.1, U.properParent (U.localParent e.2))

def topParentOf (_e : U.Edge) : PUnit := PUnit.unit

theorem edgeCarrier_subset_component (e : U.Edge) :
    U.edgeCarrier e ⊆ U.componentCarrier e.1 := by
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- Different choices are genuinely vertex-disjoint in G0. -/
theorem componentCarrier_disjoint
    (c d : C) (hcd : c ≠ d) :
    Disjoint (U.componentCarrier c) (U.componentCarrier d) := by
  rw [Set.disjoint_left]
  intro z hzC hzD
  obtain ⟨x, hx⟩ := hzC
  obtain ⟨y, hy⟩ := hzD
  exact hcd (congrArg Prod.fst (hx.trans hy.symm))

/-- Proper-cut wagon labels retain the choice tag. -/
theorem properParent_ne_of_choice_ne
    (e f : U.Edge) (hChoice : e.1 ≠ f.1) :
    U.properParentOf e ≠ U.properParentOf f := by
  intro h
  have hPair :
      (e.1, U.properParent (U.localParent e.2)) =
        (f.1, U.properParent (U.localParent f.2)) := by
    simpa only [properParentOf] using h
  exact hChoice (congrArg (fun z : C × Q => z.1) hPair)

/-- The universal top deliberately forgets the choice tag. -/
theorem topParent_eq (e f : U.Edge) :
    U.topParentOf e = U.topParentOf f := rfl

def targetCarrier (c : C) : Set U.Vertex :=
  U.placeVertex c '' Set.range (Sum.inl : V → U.LocalVertex)

def targetEdges (c : C) : Set U.Edge :=
  {e | e.1 = c ∧ e.2 ∈ U.selected}

noncomputable def data : OrderOneData U.Vertex U.Edge C U.ProperWagon where
  edgeCarrier := U.edgeCarrier
  copyCarrier := U.targetCarrier
  copyEdges := U.targetEdges
  parent := U.properParentOf

theorem targetCarrier_subset_component (c : C) :
    U.targetCarrier c ⊆ U.componentCarrier c := by
  rintro z ⟨w, _hw, rfl⟩
  exact ⟨w, rfl⟩

theorem targetEdges_subset_component (c : C) :
    U.targetEdges c ⊆ U.componentEdges c := by
  intro e he
  exact he.1

theorem selected_edge_carrier_target {c : C} {e : U.Edge}
    (he : e ∈ U.targetEdges c) :
    U.edgeCarrier e ⊆ U.targetCarrier c := by
  rintro z ⟨w, hw, rfl⟩
  have hOld := U.selected_inside_old e.2 he.2 hw
  obtain ⟨x, hx⟩ := hOld
  subst w
  exact ⟨Sum.inl x, ⟨x, rfl⟩, by simp only [he.1]⟩

/-- Same-choice proper-cut intersections are exactly the local condition.
Different choices cannot enter one component at all. -/
noncomputable def componentGeometry (c : C) :
    (U.data).ComponentTargetGeometry c where
  componentEdges := U.componentEdges c
  inter_wagon_intersections := by
    intro e he f hf hParent z hzE hzF
    have hc : e.1 = c := he
    have hfc : f.1 = c := hf
    have hLocalParent :
        U.properParent (U.localParent e.2) ≠
          U.properParent (U.localParent f.2) := by
      intro h
      apply hParent
      change (e.1, U.properParent (U.localParent e.2)) =
        (f.1, U.properParent (U.localParent f.2))
      simpa only [hc, hfc] using congrArg (Prod.mk c) h
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hxy : x = y := by
      apply U.placeVertex_injective c
      simpa only [hc, hfc] using hxz.trans hyz.symm
    subst y
    have hOld := U.local_inter_proper e.2 f.2 hLocalParent x hx hy
    obtain ⟨v, hv⟩ := hOld
    have hxz' : U.placeVertex c x = z := by
      simpa only [hc] using hxz
    refine ⟨Sum.inl v, ⟨v, rfl⟩, ?_⟩
    exact (congrArg (U.placeVertex c) hv).trans hxz'
  strong_target := by
    intro e he x y hxy hxE hyE hxT hyT
    have hc : e.1 = c := he
    obtain ⟨xLocal, hxOld, hxPlace⟩ := hxT
    obtain ⟨x0, hx0⟩ := hxOld
    obtain ⟨yLocal, hyOld, hyPlace⟩ := hyT
    obtain ⟨y0, hy0⟩ := hyOld
    subst xLocal
    subst yLocal
    have hxLocal : Sum.inl x0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwx⟩ := hxE
      have hEq : U.placeVertex c w = U.placeVertex c (Sum.inl x0) := by
        simpa only [hc] using hwx.trans hxPlace.symm
      have := U.placeVertex_injective c hEq
      simpa only [this] using hw
    have hyLocal : Sum.inl y0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwy⟩ := hyE
      have hEq : U.placeVertex c w = U.placeVertex c (Sum.inl y0) := by
        simpa only [hc] using hwy.trans hyPlace.symm
      have := U.placeVertex_injective c hEq
      simpa only [this] using hw
    have hxy0 : x0 ≠ y0 := by
      intro h
      subst y0
      exact hxy (hxPlace.symm.trans hyPlace)
    exact ⟨hc, U.local_strong e.2 x0 y0 hxy0 hxLocal hyLocal⟩
  pointwise_cover := by
    intro e he x hxE hxT
    have hc : e.1 = c := he
    obtain ⟨xLocal, hxOld, hxPlace⟩ := hxT
    obtain ⟨x0, hx0⟩ := hxOld
    subst xLocal
    have hxLocal : Sum.inl x0 ∈ U.localCarrier e.2 := by
      obtain ⟨w, hw, hwx⟩ := hxE
      have hEq : U.placeVertex c w = U.placeVertex c (Sum.inl x0) := by
        simpa only [hc] using hwx.trans hxPlace.symm
      have := U.placeVertex_injective c hEq
      simpa only [this] using hw
    obtain ⟨f, hfSel, hfParent, hxf⟩ := U.local_cover e.2 x0 hxLocal
    refine ⟨(c, f), ?_, ?_, ?_⟩
    · exact ⟨rfl, hfSel⟩
    · change (c, U.properParent (U.localParent f)) =
        (e.1, U.properParent (U.localParent e.2))
      simpa only [hc] using congrArg (Prod.mk c) hfParent
    · exact ⟨Sum.inl x0, hxf, hxPlace⟩


/-- Treat the whole choice union as one old designated parent at a proper cut. -/
noncomputable def oldData : OrderOneData U.Vertex U.Edge PUnit U.ProperWagon where
  edgeCarrier := U.edgeCarrier
  copyCarrier := fun _ => Set.univ
  copyEdges := fun _ => Set.univ
  parent := U.properParentOf

/-- Each choice is a designated target inside the single old parent. -/
noncomputable def designatedFamily :
    OrderOneData.DesignatedSubcopyFamily U.oldData C where
  containingCopy := fun _ => PUnit.unit
  copyCarrier := U.targetCarrier
  copyEdges := U.targetEdges
  carrier_subset := by
    intro c z hz
    exact Set.mem_univ z
  edges_subset := by
    intro c e he
    exact Set.mem_univ e
  siblings_vertex_disjoint := by
    intro c d hcd _hParent
    rw [Set.disjoint_left]
    intro z hzC hzD
    exact (Set.disjoint_left.mp (U.componentCarrier_disjoint c d hcd))
      (U.targetCarrier_subset_component c hzC)
      (U.targetCarrier_subset_component d hzD)
  siblings_wagon_disjoint := by
    intro c d hcd _hParent e f he hf
    exact U.properParent_ne_of_choice_ne e f
      (by simpa only [he.1, hf.1] using hcd)

/-- The choice tags construct the full component decomposition used by
the designated-subcopy scattering theorem. -/
noncomputable def componentDecomposition :
    U.designatedFamily.ComponentDecomposition where
  componentCarrier := U.componentCarrier
  componentEdges := U.componentEdges
  component_carrier_subset := by
    intro c z hz
    exact Set.mem_univ z
  component_edges_subset := by
    intro c e he
    exact Set.mem_univ e
  target_carrier_subset := U.targetCarrier_subset_component
  target_edges_subset := U.targetEdges_subset_component
  edge_carrier_subset := by
    intro c e he
    have hc : e.1 = c := he
    rw [← hc]
    exact U.edgeCarrier_subset_component e
  siblings_vertex_disjoint := by
    intro c d hcd _hParent
    exact U.componentCarrier_disjoint c d hcd
  siblings_wagon_disjoint := by
    intro c d hcd _hParent e f he hf
    exact U.properParent_ne_of_choice_ne e f
      (by
        have hc : e.1 = c := he
        have hd : f.1 = d := hf
        intro h
        apply hcd
        exact hc.symm.trans (h.trans hd))
  old_edges_covered := by
    intro i e _he
    refine ⟨e.1, Subsingleton.elim _ _, ?_⟩
    rfl

@[simp] theorem designatedFamily_target_eq_data :
    U.designatedFamily.target = U.data := rfl

/-- The tagged proper-cut assembly is now enough to apply the checked
component scattering theorem. The only remaining system input is the
old full-system-girth bound on the single parent. -/
theorem target_fullSystemGirthGT_of_old {g : ℕ}
    (hGirth : U.oldData.FullSystemGirthGT g) :
    U.data.FullSystemGirthGT g := by
  rw [← U.designatedFamily_target_eq_data]
  exact U.designatedFamily.fullSystemGirthGT_of_components
    U.componentDecomposition U.componentGeometry
    (fun _ => rfl) hGirth

end TaggedChoiceInput

namespace PrivateWagonInput

variable {V P X C Q : Type v}

/-- The verified private first-wagon extension supplies all local premises
needed by the tagged choice assembly at an arbitrary proper-cut parent map. -/
noncomputable def taggedChoiceInput
    (U : PrivateWagonInput V P X) (parent : P → Q) :
    TaggedChoiceInput C V U.PrivateVertex U.Edge P Q where
  localCarrier := U.edgeCarrier
  localParent := Prod.fst
  properParent := parent
  selected := U.targetEdges
  selected_inside_old := by
    intro e he
    exact U.selected_carrier_old e he
  local_strong := by
    intro e x y hxy hx hy
    let G := U.componentGeometry parent
    exact G.strong_target e (Set.mem_univ e) (Sum.inl x) (Sum.inl y)
      (by simpa using hxy) hx hy ⟨x, rfl⟩ ⟨y, rfl⟩
  local_cover := by
    intro e x hx
    let G := U.componentGeometry parent
    obtain ⟨f, hf, hParent, hxf⟩ :=
      G.pointwise_cover e (Set.mem_univ e) (Sum.inl x) hx ⟨x, rfl⟩
    exact ⟨f, hf, hParent, hxf⟩
  local_inter_proper := by
    intro e f hParent z hzE hzF
    let G := U.componentGeometry parent
    exact G.inter_wagon_intersections e (Set.mem_univ e) f (Set.mem_univ f)
      hParent z hzE hzF

/-- Direct application wrapper: once one private extension is given, the
choice-tagged proper-cut target inherits the old one-parent full-system
bound with no additional scattering hypotheses. -/
theorem taggedChoice_target_fullSystemGirthGT_of_old
    (U : PrivateWagonInput V P X) (C : Type v) (parent : P → Q) {g : ℕ}
    (hGirth :
      ((U.taggedChoiceInput (C := C) parent).oldData).FullSystemGirthGT g) :
    ((U.taggedChoiceInput (C := C) parent).data).FullSystemGirthGT g :=
  (U.taggedChoiceInput (C := C) parent).target_fullSystemGirthGT_of_old hGirth

end PrivateWagonInput
end StructuralRamsey.Girth
