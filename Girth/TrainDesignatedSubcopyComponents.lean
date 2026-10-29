import Girth.TrainDesignatedSubcopyProjection
import Girth.TrainDesignatedSubcopyPullback
import Girth.TrainCyclicOwnerRuns

/-!
# Circulation: a parent-contained cycle lies in one component

Section 13's scattering construction decomposes each old designated copy
into vertex- and wagon-disjoint components, each carrying one target. A
target-labelled cycle whose labels all belong to one old parent must lie
in a single component. Here that conclusion is proved from the actual
component cover and disjointness hypotheses, rather than supplied as an
opaque confinement assumption.

Target occurrences own their own components. For an actual edge occurrence,
the old-parent edge cover supplies a component owner. Incidence at each
shared connector forces adjacent owners to agree; the existing finite
cyclic-owner constancy theorem then makes every owner equal to the owner of
the retained target occurrence.

The final wrapper combines this derived localization with the checked
component supremacy and literal replacement pullback. Its confinement input
mentions only the old parent, not the component that must be discovered.

No acceptability, linearity, system-girth bound, or source-length-three
assumption is needed for this geometric localization. This does not yet
construct the cycle obtained by refining an old supreme replacement plan:
its literal target-labelled legality, including the length-two case,
remains a separate construction obligation. No ambient edges are removed.
-/

namespace StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily

universe v
variable {V E I J P : Type v}
variable {D : OrderOneData V E I P} (S : DesignatedSubcopyFamily D J)

/-- The components of each old designated copy, indexed by their targets.
The sibling separation is imposed on entire components, not merely on the
smaller targets. Every old designated edge belongs to a component with the
correct old parent. -/
structure ComponentDecomposition where
  componentCarrier : J → Set V
  componentEdges : J → Set E
  component_carrier_subset : ∀ j,
    componentCarrier j ⊆ D.copyCarrier (S.containingCopy j)
  component_edges_subset : ∀ j,
    componentEdges j ⊆ D.copyEdges (S.containingCopy j)
  target_carrier_subset : ∀ j, S.copyCarrier j ⊆ componentCarrier j
  target_edges_subset : ∀ j, S.copyEdges j ⊆ componentEdges j
  edge_carrier_subset : ∀ j e, e ∈ componentEdges j →
    D.edgeCarrier e ⊆ componentCarrier j
  siblings_vertex_disjoint : ∀ j k, j ≠ k → S.containingCopy j = S.containingCopy k →
    Disjoint (componentCarrier j) (componentCarrier k)
  siblings_wagon_disjoint : ∀ j k, j ≠ k → S.containingCopy j = S.containingCopy k →
    ∀ e f, e ∈ componentEdges j → f ∈ componentEdges k → D.parent e ≠ D.parent f
  old_edges_covered : ∀ i e, e ∈ D.copyEdges i →
    ∃ j, S.containingCopy j = i ∧ e ∈ componentEdges j

namespace ComponentDecomposition

variable {S} (K : S.ComponentDecomposition)

/-- A component owns its own target label and its actual edge labels. -/
def Owns (j : J) (a : J ⊕ E) : Prop :=
  a = Sum.inl j ∨ ∃ e, a = Sum.inr e ∧ e ∈ K.componentEdges j

/-- An owned label has all its vertices in the component carrier. -/
theorem owned_carrier_subset (j : J) (a : J ⊕ E) (h : K.Owns j a) :
    S.target.carrier a ⊆ K.componentCarrier j := by
  rcases h with hTarget | ⟨e, hEdge, he⟩
  · rw [hTarget]
    change S.copyCarrier j ⊆ K.componentCarrier j
    exact K.target_carrier_subset j
  · rw [hEdge]
    change D.edgeCarrier e ⊆ K.componentCarrier j
    exact K.edge_carrier_subset j e he

/-- An owned label uses only component edges; this also handles wagon
incidence of a target whose edge set is smaller than its component's. -/
theorem owned_edges_subset (j : J) (a : J ⊕ E) (h : K.Owns j a) :
    S.target.edges a ⊆ K.componentEdges j := by
  rcases h with hTarget | ⟨e, hEdge, he⟩
  · rw [hTarget]
    change S.copyEdges j ⊆ K.componentEdges j
    exact K.target_edges_subset j
  · rw [hEdge]
    intro f hf
    change f = e at hf
    subst f
    exact he

/-- Labels with a common connector and a common old parent have the same
component owner. Both kinds of connector are treated physically. -/
theorem owners_eq_of_shared_connector
    (j k : J) (hParent : S.containingCopy j = S.containingCopy k)
    (a b : J ⊕ E) (c : V ⊕ P)
    (ha : K.Owns j a) (hb : K.Owns k b)
    (hIncA : S.target.Incident a c) (hIncB : S.target.Incident b c) : j = k := by
  by_contra hjk
  cases c with
  | inl x =>
      change x ∈ S.target.carrier a at hIncA
      change x ∈ S.target.carrier b at hIncB
      exact (Set.disjoint_left.mp (K.siblings_vertex_disjoint j k hjk hParent))
        (K.owned_carrier_subset j a ha hIncA)
        (K.owned_carrier_subset k b hb hIncB)
  | inr p =>
      change ∃ e, e ∈ S.target.edges a ∧ D.parent e = p at hIncA
      change ∃ f, f ∈ S.target.edges b ∧ D.parent f = p at hIncB
      obtain ⟨e, he, hep⟩ := hIncA
      obtain ⟨f, hf, hfp⟩ := hIncB
      exact K.siblings_wagon_disjoint j k hjk hParent e f
        (K.owned_edges_subset j a ha he)
        (K.owned_edges_subset k b hb hf) (hep.trans hfp.symm)

/-- Every label of a genuine cycle contained in one old parent lies in the
component of any retained target occurrence. The confinement conclusion is
derived from component disjointness and the actual cyclic incidences.

There is no acceptability or system-girth hypothesis, and the proof works
unchanged at length two. Constructing the required parent-contained cycle
from an old supreme plan is a separate step. -/
theorem cycle_labels_in_retained_component
    {n : ℕ} (B : S.target.BigCycle n) (oldParent : I)
    (hParentLabels : ∀ t : Fin n,
      match B.label t with
      | .inl j => S.containingCopy j = oldParent
      | .inr e => e ∈ D.copyEdges oldParent)
    (target : J) (k : Fin n) (hk : B.label k = Sum.inl target) :
    ∀ t : Fin n, B.label t = Sum.inl target ∨
      ∃ e, B.label t = Sum.inr e ∧ e ∈ K.componentEdges target := by
  classical
  have hOwners : ∀ t : Fin n,
      ∃ j, S.containingCopy j = oldParent ∧ K.Owns j (B.label t) := by
    intro t
    cases hLabel : B.label t with
    | inl j =>
        refine ⟨j, ?_, Or.inl rfl⟩
        simpa only [hLabel] using hParentLabels t
    | inr e =>
        have he : e ∈ D.copyEdges oldParent := by
          simpa only [hLabel] using hParentLabels t
        obtain ⟨j, hj, hComponent⟩ := K.old_edges_covered oldParent e he
        exact ⟨j, hj, Or.inr ⟨e, rfl, hComponent⟩⟩
  choose owner hOwnerParent hOwned using hOwners
  have hAdjacent : ∀ t : Fin n, owner t = owner (cyclicSucc t) := by
    intro t
    exact K.owners_eq_of_shared_connector
      (owner t) (owner (cyclicSucc t))
      ((hOwnerParent t).trans (hOwnerParent (cyclicSucc t)).symm)
      (B.label t) (B.label (cyclicSucc t)) (B.connector t)
      (hOwned t) (hOwned (cyclicSucc t)) (B.left_incident t) (B.right_incident t)
  have hZero : cyclicOwnerChanges owner = 0 :=
    (cyclicOwnerChanges_eq_zero_iff owner).mpr hAdjacent
  have hn : 0 < n := by
    have hLength := B.length_ge_two
    omega
  obtain ⟨common, hCommon⟩ :=
    (cyclicOwnerChanges_zero_iff_constant hn owner).mp hZero
  have hOwnerTarget : owner k = target := by
    have h := hOwned k
    rcases h with hTarget | ⟨e, hEdge, _⟩
    · exact (Sum.inl.inj (hk.symm.trans hTarget)).symm
    · have : (Sum.inl target : J ⊕ E) = Sum.inr e := hk.symm.trans hEdge
      cases this
  intro t
  have ht : owner t = target :=
    (hCommon t).trans ((hCommon k).symm.trans hOwnerTarget)
  change K.Owns target (B.label t)
  rw [← ht]
  exact hOwned t

/-- An actual literal replacement whose output lies in one old parent
makes its retained target supreme in the source. Component confinement is
proved from the decomposition rather than included among the inputs.

The actual output cycle, literal replacement word and long-piece geometry
remain explicit: this is the assembly after old-plan refinement, not a
claim that refinement has already been constructed. -/
theorem supreme_of_parent_contained_replacement
    {n m : ℕ} (C : S.target.BigCycle n) (B : S.target.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : S.target.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry S.target pieces)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord S.target pieces)
    (oldParent : I)
    (hParentLabels : ∀ t : Fin m,
      match B.label t with
      | .inl j => S.containingCopy j = oldParent
      | .inr e => e ∈ D.copyEdges oldParent)
    (target : J) (G : S.target.ComponentTargetGeometry target)
    (hComponentEdges : G.componentEdges = K.componentEdges target)
    (k : Fin m) (hk : B.label k = Sum.inl target) :
    ∃ kC : Fin n, C.label kC = Sum.inl target ∧
      C.HasSupremeAt S.target kC := by
  have hLabels := K.cycle_labels_in_retained_component
    B oldParent hParentLabels target k hk
  apply C.supreme_of_localized_component_replacement
    S.target B hAccept hLinear pieces hGeom hWord target G k hk
  rw [hComponentEdges]
  exact hLabels

end ComponentDecomposition
end StructuralRamsey.Girth.OrderOneData.DesignatedSubcopyFamily
