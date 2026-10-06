import Girth.BoundaryIncidence
import Mathlib.Data.Fintype.EquivFin

/-! # Shared-vertex boundary incidence

For a finite linear family of labelled hyperedges, the vertices lying in at
least two distinct hyperedges form a finite type: choose one witnessing ordered
pair of labels for each shared vertex; linearity makes this choice injective.
Restricting the incidence graph to those shared vertices therefore gives a
finite acyclic graph whenever the full incidence graph is acyclic.
-/

namespace StructuralRamsey.Girth

universe v
variable {W E : Type v}

/-- Ambient vertices belonging to at least two distinct labelled hyperedges. -/
def SharedBoundaryVertex (edge : E → Set W) : Type v :=
  {x : W // ∃ e f : E, e ≠ f ∧ x ∈ edge e ∧ x ∈ edge f}

/-- A labelled family is linear when distinct labelled hyperedges meet in at
most one ambient vertex. -/
def LabelledEdgeLinear (edge : E → Set W) : Prop :=
  ∀ ⦃e f : E⦄, e ≠ f → (edge e ∩ edge f).Subsingleton

theorem sharedBoundaryPair_exists
    (edge : E → Set W)
    (x : SharedBoundaryVertex edge) :
    ∃ p : E × E,
      p.1 ≠ p.2 ∧ x.1 ∈ edge p.1 ∧ x.1 ∈ edge p.2 := by
  rcases x.2 with ⟨e, f, hef, hxe, hxf⟩
  exact ⟨(e, f), hef, hxe, hxf⟩

/-- A canonical witnessing ordered pair for a shared vertex. -/
noncomputable def sharedBoundaryPair
    (edge : E → Set W)
    (x : SharedBoundaryVertex edge) : E × E :=
  Classical.choose (sharedBoundaryPair_exists edge x)

theorem sharedBoundaryPair_spec
    (edge : E → Set W)
    (x : SharedBoundaryVertex edge) :
    (sharedBoundaryPair edge x).1 ≠
        (sharedBoundaryPair edge x).2 ∧
      x.1 ∈ edge (sharedBoundaryPair edge x).1 ∧
      x.1 ∈ edge (sharedBoundaryPair edge x).2 :=
  Classical.choose_spec (sharedBoundaryPair_exists edge x)

/-- Linearity makes the chosen witness-pair map injective. -/
theorem sharedBoundaryPair_injective
    (edge : E → Set W)
    (hLinear : LabelledEdgeLinear edge) :
    Function.Injective (sharedBoundaryPair edge) := by
  intro x y hxy
  have hx := sharedBoundaryPair_spec edge x
  have hy := sharedBoundaryPair_spec edge y
  have hfst :
      (sharedBoundaryPair edge x).1 =
        (sharedBoundaryPair edge y).1 :=
    congrArg Prod.fst hxy
  have hsnd :
      (sharedBoundaryPair edge x).2 =
        (sharedBoundaryPair edge y).2 :=
    congrArg Prod.snd hxy
  have hy1 :
      y.1 ∈ edge (sharedBoundaryPair edge x).1 := by
    rw [hfst]
    exact hy.2.1
  have hy2 :
      y.1 ∈ edge (sharedBoundaryPair edge x).2 := by
    rw [hsnd]
    exact hy.2.2
  apply Subtype.ext
  exact
    hLinear hx.1
      ⟨hx.2.1, hx.2.2⟩
      ⟨hy1, hy2⟩

/-- Hence shared boundary vertices are finite whenever the edge-label type is
finite. -/
theorem finite_sharedBoundaryVertex
    [Finite E]
    (edge : E → Set W)
    (hLinear : LabelledEdgeLinear edge) :
    Finite (SharedBoundaryVertex edge) :=
  Finite.of_injective
    (sharedBoundaryPair edge)
    (sharedBoundaryPair_injective edge hLinear)

/-- The edge carried by label e, restricted to genuinely shared vertices. -/
def sharedBoundaryEdge
    (edge : E → Set W)
    (e : E) :
    Set (SharedBoundaryVertex edge) :=
  {x | x.1 ∈ edge e}

/-- Inclusion of the shared-vertex incidence graph into the full incidence
graph. -/
def sharedBoundaryIncidenceHom
    (edge : E → Set W) :
    boundaryIncidenceGraph (sharedBoundaryEdge edge) →g
      boundaryIncidenceGraph edge where
  toFun z :=
    match z with
    | .inl e => Sum.inl e
    | .inr x => Sum.inr x.1
  map_rel' := by
    intro a b hab
    cases a <;> cases b <;>
      simpa [boundaryIncidenceGraph, sharedBoundaryEdge] using hab

theorem sharedBoundaryIncidenceHom_injective
    (edge : E → Set W) :
    Function.Injective (sharedBoundaryIncidenceHom edge) := by
  intro a b hab
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          simp [sharedBoundaryIncidenceHom] at hab
          subst f
          rfl
      | inr y =>
          simp [sharedBoundaryIncidenceHom] at hab
  | inr x =>
      cases b with
      | inl f =>
          simp [sharedBoundaryIncidenceHom] at hab
      | inr y =>
          simp [sharedBoundaryIncidenceHom] at hab
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hab

/-- Acyclicity passes to the incidence graph obtained by removing private
vertices. -/
theorem sharedBoundaryIncidence_isAcyclic
    (edge : E → Set W)
    (hAcyclic : (boundaryIncidenceGraph edge).IsAcyclic) :
    (boundaryIncidenceGraph (sharedBoundaryEdge edge)).IsAcyclic :=
  hAcyclic.comap
    (sharedBoundaryIncidenceHom edge)
    (sharedBoundaryIncidenceHom_injective edge)

end StructuralRamsey.Girth
