import Girth.TrainRecursiveRefinementStepGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: single-part intersections imply acyclicity

This is the base geometry of the ordinary-train refinement:
distinct physical edges sharing vertices only in one permitted
part cannot form ANY labelled Berge cycle. The bound q is arbitrary.
It is independent of the doubling proof and of the existence of
a recursive Ramsey witness.

The proof is a direct application of the existing checked
noninjective-child lemma with each edge treated as its own child.
Any purported cycle has injective physical-edge labels, producing
an immediate contradiction. Equal physical carriers may still
have distinct labels, which are handled without quotienting.

UNCOMPILED CANDIDATE: run exact-head Lean and strict axiom checks
before promoting the manuscript's single-part observation.
-/

namespace StructuralRamsey.Girth

universe v
variable {E V Part : Type v}

/-- A labelled family of transversal physical edges is Berge-acyclic
if all intersections of distinct edges use one permitted part.
This statement has no finite-girth or ambient-finiteness premise. -/
theorem labelledGirthGT_of_singlePartEdgeIntersections
    (edge : E → Set V) (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hTransversal : ∀ e : E, Set.InjOn part (edge e))
    (hIntersection : ∀ a b : E, a ≠ b →
      (edge a ∩ edge b) ⊆ part ⁻¹' allowed)
    (q : ℕ) : LabelledGirthGT edge q := by
  rintro ⟨C, _⟩
  have hNotInjective := C.child_not_injective_of_singleton_intersections
    C.label edge part allowed hAllowed
    (fun i => hTransversal (C.label i))
    (fun i => Set.Subset.rfl)
    hIntersection
  exact hNotInjective C.label_injective

/-- The corresponding unlabelled hypergraph has infinite Berge
girth. Even when different labels have equal carriers, passing to
the range cannot create a cycle. -/
theorem girthGT_of_singlePartEdgeIntersections
    (edge : E → Set V) (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hTransversal : ∀ e : E, Set.InjOn part (edge e))
    (hIntersection : ∀ a b : E, a ≠ b →
      (edge a ∩ edge b) ⊆ part ⁻¹' allowed)
    (q : ℕ) : GirthGT (Set.range edge) q :=
  (labelledGirthGT_of_singlePartEdgeIntersections
    edge part allowed hAllowed hTransversal hIntersection q).range_girth

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.labelledGirthGT_of_singlePartEdgeIntersections
#print axioms StructuralRamsey.Girth.girthGT_of_singlePartEdgeIntersections
