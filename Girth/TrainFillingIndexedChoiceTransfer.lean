import Girth.TrainFillingIndexedChoiceCore
import Girth.TrainDesignatedSubcopyGirth

set_option Elab.async false

/-!
# Choice-indexed full component scattering transfer

Uses the actual dependent sum over potentially different local embeddings
U c. The old one-parent girth bound is an explicit input; no output
cycle, supreme plan, or top-system-girth assumption is made.
-/

namespace StructuralRamsey.Girth
namespace IndexedPrivateChoice

universe v
variable {C V P X Q : Type v}
variable (U : C → PrivateWagonInput V P X) (parent : P → Q)

/-- The physical incidence system with one old parent and all choices. -/
noncomputable def oldData : OrderOneData (Vertex U) (Edge U) PUnit (ProperWagon (Q := Q) U) where
  edgeCarrier := edgeCarrier U
  copyCarrier := fun _ => Set.univ
  copyEdges := fun _ => Set.univ
  parent := properParentOf U parent

/-- The target incidence system retains each choice as its own designation. -/
noncomputable def data : OrderOneData (Vertex U) (Edge U) C (ProperWagon (Q := Q) U) where
  edgeCarrier := edgeCarrier U
  copyCarrier := targetCarrier U
  copyEdges := targetEdges U
  parent := properParentOf U parent

/-- Original choice targets form an honest designated-subcopy family. -/
noncomputable def designatedFamily :
    OrderOneData.DesignatedSubcopyFamily (oldData U parent) C where
  containingCopy := fun _ => PUnit.unit
  copyCarrier := targetCarrier U
  copyEdges := targetEdges U
  carrier_subset := fun _ _ _ => Set.mem_univ _
  edges_subset := fun _ _ _ => Set.mem_univ _
  siblings_vertex_disjoint := by
    intro c d hcd _
    rw [Set.disjoint_left]
    intro z hzC hzD
    exact (Set.disjoint_left.mp (componentCarrier_disjoint U c d hcd))
      (targetCarrier_subset_component U c hzC)
      (targetCarrier_subset_component U d hzD)
  siblings_wagon_disjoint := by
    intro c d hcd _ e f he hf
    have hc : e.1 = c := by
      obtain ⟨ec, _hm, hEc⟩ := he
      simpa only [tagEdge] using congrArg Sigma.fst hEc.symm
    have hd : f.1 = d := by
      obtain ⟨fd, _hm, hFd⟩ := hf
      simpa only [tagEdge] using congrArg Sigma.fst hFd.symm
    exact properParent_ne_of_choice_ne U parent e f (by
      intro h; exact hcd (hc.symm.trans (h.trans hd)))

/-- All choice components are disjoint siblings of one old parent. -/
noncomputable def componentDecomposition :
    (designatedFamily U parent).ComponentDecomposition where
  componentCarrier := componentCarrier U
  componentEdges := componentEdges U
  component_carrier_subset := fun _ _ _ => Set.mem_univ _
  component_edges_subset := fun _ _ _ => Set.mem_univ _
  target_carrier_subset := targetCarrier_subset_component U
  target_edges_subset := targetEdges_subset_component U
  edge_carrier_subset := by
    intro c e he
    obtain ⟨ec, rfl⟩ := he
    exact edgeCarrier_subset_component U (tagEdge U c ec)
  siblings_vertex_disjoint := by
    intro c d hcd _
    exact componentCarrier_disjoint U c d hcd
  siblings_wagon_disjoint := by
    intro c d hcd _ e f he hf
    obtain ⟨ec, hEc⟩ := he
    obtain ⟨fd, hFd⟩ := hf
    have hc : e.1 = c := by simpa [tagEdge] using congrArg Sigma.fst hEc.symm
    have hd : f.1 = d := by simpa [tagEdge] using congrArg Sigma.fst hFd.symm
    exact properParent_ne_of_choice_ne U parent e f (by
      intro h; exact hcd (hc.symm.trans (h.trans hd)))
  old_edges_covered := by
    intro _ e _
    refine ⟨e.1, Subsingleton.elim _ _, ?_⟩
    exact ⟨e.2, rfl⟩

@[simp] theorem designatedFamily_target_eq_data :
    (designatedFamily U parent).target = data U parent := rfl

/-- Each choice's verified private geometry remains valid when it is tagged
in the heterogeneous sum. No two choices need to be isomorphic. -/
noncomputable def componentGeometry (c : C) :
    (data U parent).ComponentTargetGeometry c where
  componentEdges := componentEdges U c
  inter_wagon_intersections := by
    intro e he f hf hParent z hzE hzF
    obtain ⟨a, rfl⟩ := he
    obtain ⟨b, rfl⟩ := hf
    have hLocalParent : parent a.1 ≠ parent b.1 := by
      intro h
      apply hParent
      change (c, parent a.1) = (c, parent b.1)
      exact congrArg (Prod.mk c) h
    obtain ⟨x, hx, hxz⟩ := hzE
    obtain ⟨y, hy, hyz⟩ := hzF
    have hxy : x = y := (tagVertex_injective U c) (hxz.trans hyz.symm)
    subst y
    let G := (U c).componentGeometry parent
    have hOld := G.inter_wagon_intersections a (Set.mem_univ _) b
      (Set.mem_univ _) hLocalParent x hx hy
    exact ⟨x, hOld, hxz⟩
  strong_target := by
    intro e he x y hxy hxE hyE hxT hyT
    obtain ⟨a, rfl⟩ := he
    obtain ⟨x0, hxOld, hxPlace⟩ := hxT
    obtain ⟨y0, hyOld, hyPlace⟩ := hyT
    have hxLocal : x0 ∈ (U c).edgeCarrier a := by
      obtain ⟨w, hw, hwx⟩ := hxE
      have h := (tagVertex_injective U c) (hwx.trans hxPlace.symm)
      simpa only [tagEdge, h] using hw
    have hyLocal : y0 ∈ (U c).edgeCarrier a := by
      obtain ⟨w, hw, hwy⟩ := hyE
      have h := (tagVertex_injective U c) (hwy.trans hyPlace.symm)
      simpa only [tagEdge, h] using hw
    have hxyLocal : x0 ≠ y0 := by
      intro h
      subst y0
      exact hxy (hxPlace.symm.trans hyPlace)
    let G := (U c).componentGeometry parent
    have hSelected := G.strong_target a (Set.mem_univ _) x0 y0
      hxyLocal hxLocal hyLocal hxOld hyOld
    exact ⟨a, hSelected, rfl⟩
  pointwise_cover := by
    intro e he z hzE hzT
    obtain ⟨a, rfl⟩ := he
    obtain ⟨x, hxOld, hxPlace⟩ := hzT
    have hxLocal : x ∈ (U c).edgeCarrier a := by
      obtain ⟨w, hw, hwz⟩ := hzE
      have h := (tagVertex_injective U c) (hwz.trans hxPlace.symm)
      simpa only [tagEdge, h] using hw
    let G := (U c).componentGeometry parent
    obtain ⟨f, hfSelected, hfParent, hxf⟩ :=
      G.pointwise_cover a (Set.mem_univ _) x hxLocal hxOld
    refine ⟨tagEdge U c f, ?_, ?_, ?_⟩
    · exact ⟨f, hfSelected, rfl⟩
    · change (c, parent f.1) = (c, parent a.1)
      exact congrArg (Prod.mk c) hfParent
    · exact ⟨x, hxf, hxPlace⟩

/-- Full transfer of system girth is conditional only on the full old bound.
It adds no fabricated output girth or supreme-plan assumption. -/
theorem target_fullSystemGirthGT_of_old {g : ℕ}
    (hOld : (oldData U parent).FullSystemGirthGT g) :
    (data U parent).FullSystemGirthGT g := by
  rw [← designatedFamily_target_eq_data U parent]
  exact (designatedFamily U parent).fullSystemGirthGT_of_components
    (componentDecomposition U parent) (componentGeometry U parent)
    (fun _ => rfl) hOld

end IndexedPrivateChoice
end StructuralRamsey.Girth
