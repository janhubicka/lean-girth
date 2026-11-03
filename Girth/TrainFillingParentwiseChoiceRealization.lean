import Girth.TrainFillingTaggedChoiceAssembly

set_option Elab.async false

/-!
# Parentwise realization of tagged choice components

The local tagged G0 assembly is copied into every selected old parent.
Different old parents may overlap arbitrarily; only choices with the SAME
old parent must be disjoint. This is exactly the scope of
DesignatedSubcopyFamily and ComponentDecomposition.

A realization supplies injective maps of local vertices, physical edges and
proper-cut wagon labels into the actual ambient incidence system, together
with exact carrier, parent and old-copy image identities. From these data we
construct the global target family indexed by (old parent, choice), its
component decomposition, and its target geometry. The checked scattering
theorem then transfers FullSystemGirthGT globally in one step.

No disjointness between different old parents is assumed.
-/

namespace StructuralRamsey.Girth

universe v

namespace TaggedChoiceInput

variable {C LV LY LE LP LQ V E I P : Type v}
variable (U : TaggedChoiceInput C LV LY LE LP LQ)
variable (D : OrderOneData V E I P)

/-- Exact physical realization of one complete tagged choice union inside
EVERY old designated parent. Parent copies may overlap with each other. -/
structure ParentwiseRealization where
  vertex : I → U.Vertex ↪ V
  edge : I → U.Edge ↪ E
  wagon : I → U.ProperWagon ↪ P
  edgeCarrier_eq : ∀ i e,
    D.edgeCarrier (edge i e) = vertex i '' U.edgeCarrier e
  parent_eq : ∀ i e,
    D.parent (edge i e) = wagon i (U.properParentOf e)
  copyCarrier_eq : ∀ i, D.copyCarrier i = Set.range (vertex i)
  copyEdges_eq : ∀ i, D.copyEdges i = Set.range (edge i)

namespace ParentwiseRealization

variable {U D} (R : ParentwiseRealization U D)

abbrev Target (_R : ParentwiseRealization U D) := I × C

def targetCarrier (j : R.Target) : Set V :=
  R.vertex j.1 '' U.targetCarrier j.2

def targetEdges (j : R.Target) : Set E :=
  R.edge j.1 '' U.targetEdges j.2

def componentCarrier (j : R.Target) : Set V :=
  R.vertex j.1 '' U.componentCarrier j.2

def componentEdges (j : R.Target) : Set E :=
  R.edge j.1 '' U.componentEdges j.2

theorem targetCarrier_subset_component (j : R.Target) :
    R.targetCarrier j ⊆ R.componentCarrier j := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, U.targetCarrier_subset_component j.2 hx, rfl⟩

theorem targetEdges_subset_component (j : R.Target) :
    R.targetEdges j ⊆ R.componentEdges j := by
  rintro e ⟨a, ha, rfl⟩
  exact ⟨a, U.targetEdges_subset_component j.2 ha, rfl⟩

theorem componentCarrier_subset_parent (j : R.Target) :
    R.componentCarrier j ⊆ D.copyCarrier j.1 := by
  rintro z ⟨x, hx, rfl⟩
  rw [R.copyCarrier_eq j.1]
  exact ⟨x, rfl⟩

theorem componentEdges_subset_parent (j : R.Target) :
    R.componentEdges j ⊆ D.copyEdges j.1 := by
  rintro e ⟨a, ha, rfl⟩
  rw [R.copyEdges_eq j.1]
  exact ⟨a, rfl⟩

theorem edge_carrier_subset_component (j : R.Target) (e : E)
    (he : e ∈ R.componentEdges j) :
    D.edgeCarrier e ⊆ R.componentCarrier j := by
  obtain ⟨a, ha, rfl⟩ := he
  rw [R.edgeCarrier_eq j.1 a]
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, U.edgeCarrier_subset_component a hx, rfl⟩

/-- Siblings under one old parent remain vertex-disjoint after realization. -/
theorem sibling_componentCarrier_disjoint
    (j k : R.Target) (hjk : j ≠ k) (hParent : j.1 = k.1) :
    Disjoint (R.componentCarrier j) (R.componentCarrier k) := by
  subst k.1
  have hChoice : j.2 ≠ k.2 := by
    intro h
    exact hjk (Prod.ext rfl h)
  rw [Set.disjoint_left]
  intro z hzJ hzK
  obtain ⟨x, hx, hxz⟩ := hzJ
  obtain ⟨y, hy, hyz⟩ := hzK
  have hxy : x = y := R.vertex j.1 |>.injective (hxz.trans hyz.symm)
  subst y
  exact (Set.disjoint_left.mp
    (U.componentCarrier_disjoint j.2 k.2 hChoice)) hx hy

/-- Siblings under one old parent remain proper-wagon-disjoint. -/
theorem sibling_componentWagon_disjoint
    (j k : R.Target) (hjk : j ≠ k) (hParent : j.1 = k.1)
    (e f : E) (he : e ∈ R.componentEdges j)
    (hf : f ∈ R.componentEdges k) :
    D.parent e ≠ D.parent f := by
  subst k.1
  have hChoice : j.2 ≠ k.2 := by
    intro h
    exact hjk (Prod.ext rfl h)
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, rfl⟩ := hf
  have hab : a.1 ≠ b.1 := by
    have haChoice : a.1 = j.2 := ha
    have hbChoice : b.1 = k.2 := hb
    intro h
    apply hChoice
    exact haChoice.symm.trans (h.trans hbChoice)
  have hLocal : U.properParentOf a ≠ U.properParentOf b :=
    U.properParent_ne_of_choice_ne a b hab
  rw [R.parent_eq j.1 a, R.parent_eq j.1 b]
  intro h
  exact hLocal ((R.wagon j.1).injective h)

/-- Every old-parent edge belongs to exactly some local choice component;
only existence is needed by ComponentDecomposition. -/
theorem old_edge_covered (i : I) (e : E) (he : e ∈ D.copyEdges i) :
    ∃ j : R.Target, j.1 = i ∧ e ∈ R.componentEdges j := by
  rw [R.copyEdges_eq i] at he
  obtain ⟨a, rfl⟩ := he
  refine ⟨(i, a.1), rfl, ?_⟩
  exact ⟨a, rfl, rfl⟩

/-- Global target family: targets are local choices inside each old parent. -/
noncomputable def designatedFamily :
    OrderOneData.DesignatedSubcopyFamily D R.Target where
  containingCopy := Prod.fst
  copyCarrier := R.targetCarrier
  copyEdges := R.targetEdges
  carrier_subset := by
    intro j
    exact (R.targetCarrier_subset_component j).trans
      (R.componentCarrier_subset_parent j)
  edges_subset := by
    intro j
    exact (R.targetEdges_subset_component j).trans
      (R.componentEdges_subset_parent j)
  siblings_vertex_disjoint := by
    intro j k hjk hParent
    exact Set.disjoint_of_subset
      (R.targetCarrier_subset_component j)
      (R.targetCarrier_subset_component k)
      (R.sibling_componentCarrier_disjoint j k hjk hParent)
  siblings_wagon_disjoint := by
    intro j k hjk hParent e f he hf
    exact R.sibling_componentWagon_disjoint j k hjk hParent e f
      (R.targetEdges_subset_component j he)
      (R.targetEdges_subset_component k hf)

/-- The realized choice fibres give the complete global component
decomposition required by the scattering theorem. -/
noncomputable def componentDecomposition :
    R.designatedFamily.ComponentDecomposition where
  componentCarrier := R.componentCarrier
  componentEdges := R.componentEdges
  component_carrier_subset := R.componentCarrier_subset_parent
  component_edges_subset := R.componentEdges_subset_parent
  target_carrier_subset := R.targetCarrier_subset_component
  target_edges_subset := R.targetEdges_subset_component
  edge_carrier_subset := R.edge_carrier_subset_component
  siblings_vertex_disjoint := R.sibling_componentCarrier_disjoint
  siblings_wagon_disjoint := R.sibling_componentWagon_disjoint
  old_edges_covered := R.old_edge_covered

/-- Transport local component target geometry through the exact realization
inside one old parent. -/
noncomputable def componentGeometry (j : R.Target) :
    R.designatedFamily.target.ComponentTargetGeometry j where
  componentEdges := R.componentEdges j
  inter_wagon_intersections := by
    intro e he f hf hParent z hzE hzF
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨b, hb, rfl⟩ := hf
    have hLocalParent : U.properParentOf a ≠ U.properParentOf b := by
      intro h
      apply hParent
      rw [R.parent_eq j.1 a, R.parent_eq j.1 b]
      exact congrArg (R.wagon j.1) h
    rw [R.edgeCarrier_eq j.1 a] at hzE
    rw [R.edgeCarrier_eq j.1 b] at hzF
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hxy : x = y := (R.vertex j.1).injective (hxz.trans hyz.symm)
    subst y
    have hLocal := (U.componentGeometry j.2).inter_wagon_intersections
      a ha b hb hLocalParent x hx hy
    refine ⟨x, hLocal, hxz⟩
  strong_target := by
    intro e he x y hxy hxE hyE hxT hyT
    obtain ⟨a, ha, rfl⟩ := he
    rw [R.edgeCarrier_eq j.1 a] at hxE hyE
    obtain ⟨x0, hx0, hxMap⟩ := hxE
    obtain ⟨y0, hy0, hyMap⟩ := hyE
    obtain ⟨tx, htx, htxMap⟩ := hxT
    obtain ⟨ty, hty, htyMap⟩ := hyT
    have hxt : x0 = tx := (R.vertex j.1).injective
      (hxMap.trans htxMap.symm)
    have hyt : y0 = ty := (R.vertex j.1).injective
      (hyMap.trans htyMap.symm)
    subst tx
    subst ty
    have hxy0 : x0 ≠ y0 := by
      intro h
      subst y0
      exact hxy (hxMap.symm.trans hyMap)
    have hSelected := (U.componentGeometry j.2).strong_target
      a ha x0 y0 hxy0 hx0 hy0 htx hty
    exact ⟨a, hSelected, rfl⟩
  pointwise_cover := by
    intro e he x hxE hxT
    obtain ⟨a, ha, rfl⟩ := he
    rw [R.edgeCarrier_eq j.1 a] at hxE
    obtain ⟨x0, hx0, hxMap⟩ := hxE
    obtain ⟨tx, htx, htxMap⟩ := hxT
    have hxt : x0 = tx := (R.vertex j.1).injective
      (hxMap.trans htxMap.symm)
    subst tx
    obtain ⟨b, hbTarget, hbParent, hxb⟩ :=
      (U.componentGeometry j.2).pointwise_cover a ha x0 hx0 htx
    refine ⟨R.edge j.1 b, ?_, ?_, ?_⟩
    · exact ⟨b, hbTarget, rfl⟩
    · rw [R.parent_eq j.1 b, R.parent_eq j.1 a]
      exact congrArg (R.wagon j.1) hbParent
    · rw [R.edgeCarrier_eq j.1 b]
      exact ⟨x0, hxb, hxMap⟩

/-- Global parentwise scattering: no reduction to one parent and no
disjointness hypothesis across different old parents is needed. -/
theorem target_fullSystemGirthGT {g : ℕ}
    (hGirth : D.FullSystemGirthGT g) :
    R.designatedFamily.target.FullSystemGirthGT g := by
  exact R.designatedFamily.fullSystemGirthGT_of_components
    R.componentDecomposition R.componentGeometry (fun _ => rfl) hGirth

end ParentwiseRealization
end TaggedChoiceInput
end StructuralRamsey.Girth
