import Girth.TrainDesignatedSubcopyComponents

/-!
# Ambient strongness of targets inside separated components

The final clause of Section 13's subcopy-restriction lemma assumes that
the old designated copy is strongly induced in the ambient hypergraph,
whereas its target is initially strongly induced only in its own component.

An ambient edge meeting the target twice first belongs to the old copy.
The component edge cover assigns it an owner.  One of its target vertices
then forces that owner to be the target's component by vertex disjointness.
Only at this point is the component-local target strongness applied.

No assertion that a union of individually strong pieces is strong is used.
The argument does not require wagon linearity, acceptability, or a girth
bound, and it keeps every ambient edge.
-/

namespace StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily

universe v
variable {V E I J P : Type v}
variable {D : OrderOneData V E I P} {S : DesignatedSubcopyFamily D J}

namespace ComponentDecomposition

variable (K : S.ComponentDecomposition)

/-- An edge of an old parent that meets a target at even one vertex must
belong to that target's component.  The conclusion uses the component
cover and vertex separation, not any strongness of the component union. -/
theorem edge_in_target_component_of_old_edge
    (target : J) (e : E)
    (he : e ∈ D.copyEdges (S.containingCopy target))
    (x : V) (hxe : x ∈ D.edgeCarrier e) (hx : x ∈ S.copyCarrier target) :
    e ∈ K.componentEdges target := by
  obtain ⟨owner, hParent, hOwner⟩ :=
    K.old_edges_covered (S.containingCopy target) e he
  have hOwnerTarget : owner = target := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (K.siblings_vertex_disjoint owner target hne hParent))
      (K.edge_carrier_subset owner e hOwner hxe)
      (K.target_carrier_subset target hx)
  rw [hOwnerTarget] at hOwner
  exact hOwner

/-- Strongness of the old designated parent in the whole ambient edge
family composes with strongness of its target inside the selected component.
The conclusion is the exact two-distinct-vertex ambient strongness condition
for that target.  Component-local strongness is not silently globalized. -/
theorem target_strong_of_parent_strong
    (target : J) (G : S.target.ComponentTargetGeometry target)
    (hComponentEdges : G.componentEdges = K.componentEdges target)
    (hParentStrong : ∀ (e : E) (x y : V),
      x ≠ y → x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
      x ∈ D.copyCarrier (S.containingCopy target) →
      y ∈ D.copyCarrier (S.containingCopy target) →
      e ∈ D.copyEdges (S.containingCopy target)) :
    ∀ (e : E) (x y : V),
      x ≠ y → x ∈ D.edgeCarrier e → y ∈ D.edgeCarrier e →
      x ∈ S.copyCarrier target → y ∈ S.copyCarrier target →
      e ∈ S.copyEdges target := by
  intro e x y hxy hxe hye hx hy
  have heParent : e ∈ D.copyEdges (S.containingCopy target) :=
    hParentStrong e x y hxy hxe hye
      (S.carrier_subset target hx) (S.carrier_subset target hy)
  have heComponent : e ∈ K.componentEdges target :=
    K.edge_in_target_component_of_old_edge target e heParent x hxe hx
  have heGeometry : e ∈ G.componentEdges := by
    rw [hComponentEdges]
    exact heComponent
  exact G.strong_target e heGeometry x y hxy hxe hye hx hy

end ComponentDecomposition
end StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily
