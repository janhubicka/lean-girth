import Girth.ActiveCarrierStrong

/-! # Projected copies obtained from base support containment

For an A-partite picture over a base D, an ambient irreducible A-copy has a
projected base A-embedding.  If its entire carrier projects into the carrier
of a fixed rigid base A-copy, the projected embedding is that fixed copy.
For ordered A, rigidity is automatic.

This packages the edge projection assumption needed in the circulation
untouched-subsystem girth proof.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- A rigid base A-copy absorbs any irreducible projected A-copy whose parts
all lie inside its base carrier. -/
noncomputable def projectedCopy_of_base_carrier_subset
    (A : RelStructure L UA)
    [Finite UA]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hA : A.Irreducible)
    (β : Embedding A D)
    (a : Embedding A C.toRelStructure)
    (hSupport : ∀ x : UA, C.part (a x) ∈ copyCarrier β)
    (hRigid :
      ∀ b : Embedding A D, SameCopy b β → b = β) :
    StructuralRamsey.Partite.ProjectedEmbedding A C
      β.toFunctionEmbedding := by
  classical
  have hExists := hPartite.after_irreducible_embedding hA a
  let b : Embedding A D := Classical.choose hExists
  have hb : ∀ x : UA, b x = C.part (a x) :=
    Classical.choose_spec hExists
  have hFactor : ∀ x : UA, ∃ y : UA, b x = β y := by
    intro x
    rcases hSupport x with ⟨y, hy⟩
    exact ⟨y, (hb x).trans hy.symm⟩
  have hSame : SameCopy b β :=
    sameCopy_of_range_subset b β hFactor
  have hEq : b = β := hRigid b hSame
  refine ⟨a, ?_⟩
  intro x
  have hproj := hb x
  rw [hEq] at hproj
  exact hproj.symm

/-- Ordered A has a unique base embedding with each image carrier. -/
noncomputable def orderedProjectedCopy_of_base_carrier_subset
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (β : Embedding A₀.ordered D)
    (a : Embedding A₀.ordered C.toRelStructure)
    (hSupport : ∀ x : UA, C.part (a x) ∈ copyCarrier β) :
    StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered C
      β.toFunctionEmbedding := by
  apply projectedCopy_of_base_carrier_subset
    A₀.ordered D C hPartite
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    β a hSupport
  intro b hb
  exact ordered_embedding_eq_of_sameCopy b β hb

/-- In the ordered setting, the carrier of each support edge in a cycle
whose vertices all project into the fixed base beta-copy is represented by
a beta-projected A-embedding. -/
theorem orderedBergeCycle_edges_have_fixed_projection
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (β : Embedding A₀.ordered D)
    (c : BergeCycle (supportCopies A₀.ordered C.toRelStructure))
    (hSupport :
      ∀ j : Fin c.length, ∀ x : X, x ∈ c.edge j →
        C.part x ∈ copyCarrier β) :
    ∀ j : Fin c.length,
      ∃ a : StructuralRamsey.Partite.ProjectedEmbedding
          A₀.ordered C β.toFunctionEmbedding,
        c.edge j = copyCarrier a.val := by
  intro j
  rcases c.edge_mem j with ⟨a, ha⟩
  have hPartA : ∀ x : UA, C.part (a x) ∈ copyCarrier β := by
    intro x
    apply hSupport j (a x)
    rw [ha]
    exact ⟨x, rfl⟩
  let projected :=
    orderedProjectedCopy_of_base_carrier_subset
      A₀ D C hPartite β a hPartA
  refine ⟨projected, ?_⟩
  change c.edge j = copyCarrier a
  exact ha

end StructuralRamsey.Girth
