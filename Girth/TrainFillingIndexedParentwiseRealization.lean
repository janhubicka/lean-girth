import Girth.TrainFillingIndexedChoiceTransfer
import Girth.TrainFillingParentwiseChoiceRealization

set_option Elab.async false

/-!
# Heterogeneous parentwise realization in the full ambient system

The verified indexed G0 model permits the local selected W* to differ from
choice to choice. The verified fixed-choice parentwise model permits
different OLD designated parents to overlap. This module combines both
features: within each old parent the complete indexed G0 is realized
exactly, but no disjointness between different old parents is assumed.

The physical realization carries the entire ambient incidence structure:
all edges and wagons stay present. Its exact carrier, edge, and parent
identities are explicit input data, not conclusions of the general
scattering theorem. Constructing those maps from the actual selected
M-copies and the uniform filling H remains a separate application task.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q GV GE I GQ : Type v}
variable (U : C → PrivateWagonInput V P X) (parent : P → Q)
variable (D : OrderOneData GV GE I GQ)

/-- Realization of one genuine HETEROGENEOUS G0 into each old parent.
No injectivity of the parent-index map into the ambient system, and
no inter-parent disjointness, is assumed. -/
structure ParentwiseRealization where
  vertex : I → IndexedPrivateChoice.Vertex U ↪ GV
  edge : I → IndexedPrivateChoice.Edge U ↪ GE
  wagon : I → IndexedPrivateChoice.ProperWagon (Q := Q) U ↪ GQ
  edgeCarrier_eq : ∀ i e,
    D.edgeCarrier (edge i e) =
      vertex i '' IndexedPrivateChoice.edgeCarrier U e
  parent_eq : ∀ i e,
    D.parent (edge i e) =
      wagon i (IndexedPrivateChoice.properParentOf U parent e)
  copyCarrier_eq : ∀ i,
    D.copyCarrier i = Set.range (vertex i)
  copyEdges_eq : ∀ i,
    D.copyEdges i = Set.range (edge i)

namespace ParentwiseRealization

variable {U parent D}
variable (R : ParentwiseRealization U parent D)

abbrev Target (_R : ParentwiseRealization U parent D) := I × C

def targetCarrier (j : R.Target) : Set GV :=
  R.vertex j.1 '' IndexedPrivateChoice.targetCarrier U j.2

def targetEdges (j : R.Target) : Set GE :=
  R.edge j.1 '' IndexedPrivateChoice.targetEdges U j.2

def componentCarrier (j : R.Target) : Set GV :=
  R.vertex j.1 '' IndexedPrivateChoice.componentCarrier U j.2

def componentEdges (j : R.Target) : Set GE :=
  R.edge j.1 '' IndexedPrivateChoice.componentEdges U j.2

theorem targetCarrier_subset_component (j : R.Target) :
    R.targetCarrier j ⊆ R.componentCarrier j := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, IndexedPrivateChoice.targetCarrier_subset_component U j.2 hx, rfl⟩

theorem targetEdges_subset_component (j : R.Target) :
    R.targetEdges j ⊆ R.componentEdges j := by
  rintro e ⟨a, ha, rfl⟩
  exact ⟨a, IndexedPrivateChoice.targetEdges_subset_component U j.2 ha, rfl⟩

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

theorem edge_carrier_subset_component
    (j : R.Target) (e : GE)
    (he : e ∈ R.componentEdges j) :
    D.edgeCarrier e ⊆ R.componentCarrier j := by
  obtain ⟨a, ha, rfl⟩ := he
  rw [R.edgeCarrier_eq j.1 a]
  rintro z ⟨x, hx, rfl⟩
  have hIn : x ∈ IndexedPrivateChoice.componentCarrier U j.2 := by
    have hOwner : a.1 = j.2 := by
      obtain ⟨b, hb⟩ := ha
      simpa only [IndexedPrivateChoice.tagEdge] using
        congrArg Sigma.fst hb.symm
    have hLocal := IndexedPrivateChoice.edgeCarrier_subset_component U a hx
    simpa only [hOwner] using hLocal
  exact ⟨x, hIn, rfl⟩

theorem sibling_componentCarrier_disjoint
    (j k : R.Target) (hjk : j ≠ k) (hParent : j.1 = k.1) :
    Disjoint (R.componentCarrier j) (R.componentCarrier k) := by
  rcases j with ⟨i, c⟩
  rcases k with ⟨i', d⟩
  change i = i' at hParent
  subst i'
  have hChoice : c ≠ d := by
    intro h
    exact hjk (Prod.ext rfl h)
  rw [Set.disjoint_left]
  intro z hzJ hzK
  obtain ⟨x, hx, hxz⟩ := hzJ
  obtain ⟨y, hy, hyz⟩ := hzK
  have hxy : x = y := (R.vertex i).injective (hxz.trans hyz.symm)
  subst y
  exact (Set.disjoint_left.mp
    (IndexedPrivateChoice.componentCarrier_disjoint U c d hChoice)) hx hy

theorem sibling_componentWagon_disjoint
    (j k : R.Target) (hjk : j ≠ k) (hParent : j.1 = k.1)
    (e f : GE) (he : e ∈ R.componentEdges j)
    (hf : f ∈ R.componentEdges k) :
    D.parent e ≠ D.parent f := by
  rcases j with ⟨i, c⟩
  rcases k with ⟨i', d⟩
  change i = i' at hParent
  subst i'
  have hChoice : c ≠ d := by
    intro h
    exact hjk (Prod.ext rfl h)
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, rfl⟩ := hf
  have hab : a.1 ≠ b.1 := by
    have haChoice : a.1 = c := by
      obtain ⟨la, hla⟩ := ha
      simpa only [IndexedPrivateChoice.tagEdge] using
        congrArg Sigma.fst hla.symm
    have hbChoice : b.1 = d := by
      obtain ⟨lb, hlb⟩ := hb
      simpa only [IndexedPrivateChoice.tagEdge] using
        congrArg Sigma.fst hlb.symm
    intro h
    apply hChoice
    exact haChoice.symm.trans (h.trans hbChoice)
  have hLocal :
      IndexedPrivateChoice.properParentOf U parent a ≠
        IndexedPrivateChoice.properParentOf U parent b :=
    IndexedPrivateChoice.properParent_ne_of_choice_ne U parent a b hab
  rw [R.parent_eq i a, R.parent_eq i b]
  intro h
  exact hLocal ((R.wagon i).injective h)

/-- Every physical edge of each old designated parent belongs to a
choice component. This follows from the exact edge-copy equality. -/
theorem old_edge_covered (i : I) (e : GE) (he : e ∈ D.copyEdges i) :
    ∃ j : R.Target, j.1 = i ∧ e ∈ R.componentEdges j := by
  rw [R.copyEdges_eq i] at he
  obtain ⟨a, rfl⟩ := he
  refine ⟨(i, a.1), rfl, ?_⟩
  exact ⟨a, ⟨a.2, rfl⟩, rfl⟩

/-- Construct the actual target family in the unchanged global ambient
system, indexed by (old M-copy, selected W* choice). -/
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

/-- The full global component-decomposition used in scattering. -/
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

/-- Transfer each choice's local geometry through its actual injective
vertex, edge and wagon maps into the complete global incidence system. -/
noncomputable def componentGeometry (j : R.Target) :
    R.designatedFamily.target.ComponentTargetGeometry j where
  componentEdges := R.componentEdges j
  inter_wagon_intersections := by
    intro e he f hf hParent z hzE hzF
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨b, hb, rfl⟩ := hf
    change D.parent (R.edge j.1 a) ≠
      D.parent (R.edge j.1 b) at hParent
    have hLocalParent :
        IndexedPrivateChoice.properParentOf U parent a ≠
          IndexedPrivateChoice.properParentOf U parent b := by
      intro h
      apply hParent
      rw [R.parent_eq j.1 a, R.parent_eq j.1 b]
      exact congrArg (R.wagon j.1) h
    change z ∈ D.edgeCarrier (R.edge j.1 a) at hzE
    change z ∈ D.edgeCarrier (R.edge j.1 b) at hzF
    rw [R.edgeCarrier_eq j.1 a] at hzE
    rw [R.edgeCarrier_eq j.1 b] at hzF
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hxy : x = y := (R.vertex j.1).injective
      (hxz.trans hyz.symm)
    subst y
    have hLocal :=
      (IndexedPrivateChoice.componentGeometry U parent j.2).inter_wagon_intersections
        a ha b hb hLocalParent x hx hy
    exact ⟨x, hLocal, hxz⟩
  strong_target := by
    intro e he x y hxy hxE hyE hxT hyT
    obtain ⟨a, ha, rfl⟩ := he
    change x ∈ D.edgeCarrier (R.edge j.1 a) at hxE
    change y ∈ D.edgeCarrier (R.edge j.1 a) at hyE
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
    have hSelected :=
      (IndexedPrivateChoice.componentGeometry U parent j.2).strong_target
        a ha x0 y0 hxy0 hx0 hy0 htx hty
    exact ⟨a, hSelected, rfl⟩
  pointwise_cover := by
    intro e he x hxE hxT
    obtain ⟨a, ha, rfl⟩ := he
    change x ∈ D.edgeCarrier (R.edge j.1 a) at hxE
    rw [R.edgeCarrier_eq j.1 a] at hxE
    obtain ⟨x0, hx0, hxMap⟩ := hxE
    obtain ⟨tx, htx, htxMap⟩ := hxT
    have hxt : x0 = tx := (R.vertex j.1).injective
      (hxMap.trans htxMap.symm)
    subst tx
    obtain ⟨b, hbTarget, hbParent, hxb⟩ :=
      (IndexedPrivateChoice.componentGeometry U parent j.2).pointwise_cover
        a ha x0 hx0 htx
    refine ⟨R.edge j.1 b, ?_, ?_, ?_⟩
    · exact ⟨b, hbTarget, rfl⟩
    · change D.parent (R.edge j.1 b) =
        D.parent (R.edge j.1 a)
      rw [R.parent_eq j.1 b, R.parent_eq j.1 a]
      exact congrArg (R.wagon j.1) hbParent
    · change x ∈ D.edgeCarrier (R.edge j.1 b)
      rw [R.edgeCarrier_eq j.1 b]
      exact ⟨x0, hxb, hxMap⟩

/-- Global scattering is obtained in one step, with NO disjointness
between different old M-copies and NO deleted ambient edges. -/
theorem target_fullSystemGirthGT {g : ℕ}
    (hGirth : D.FullSystemGirthGT g) :
    R.designatedFamily.target.FullSystemGirthGT g := by
  exact R.designatedFamily.fullSystemGirthGT_of_components
    R.componentDecomposition R.componentGeometry (fun _ => rfl) hGirth

end ParentwiseRealization
end StructuralRamsey.Girth.IndexedPrivateChoice
