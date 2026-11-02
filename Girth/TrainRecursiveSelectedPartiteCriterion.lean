import Girth.TrainRecursiveActivePartite
import Girth.DesignatedPicture

set_option autoImplicit false

/-!
# Selected-copy labels do not automatically give partite gluing maps

The recursive fine witness and the actual partite gluing construction
use two different kinds of embedding.  A selected copy of a relational
target is projected onto a BASE EMBEDDING, while the local gluing map
must preserve the canonical A-part map of the true active subsystem.

For a selected copy of the whole active target, the required partite
embedding exists with the SAME underlying relational embedding if and
only if its base embedding agrees pointwise with the active part map.

There is a concrete obstruction: two distinct old projected A-copies
with different physical carriers give two distinct active vertices in
the same A-part.  An injective selected-copy base embedding cannot agree
with that noninjective active part map on both vertices.  Consequently
canonical selected-copy indices, although adequate for transporting the
exact OrderOneData system-girth record, cannot simply be substituted
for the actual partite gluing family in a nontrivial active fibre.

This closes an interface diagnostic, NOT the local recursive witness,
the partite Ramsey family or the attached-output supreme-cycle bound.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y : Type v}

section Criterion

variable (A : RelStructure L UA)
variable (C : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (E : StructuralRamsey.Partite.System L UA Y)
variable (D : RelStructure L UA)

local notation "Source" =>
  C.toRelStructure.induce (activeCarrier A C α)

/-- A selected relational copy of the entire actual active target is a
partite gluing map with that same embedding exactly when its injective
prescribed base projection is the literal active source part map. -/
theorem selectedCopy_isPartiteGluing_iff_basePart
    (family : Set (Embedding Source D))
    (q : DesignatedCopy Source D E family) :
    (∃ g : StructuralRamsey.Partite.Embedding
      (actualActiveSubsystemPartite A C α) E,
      g.toEmbedding = q.embedding) ↔
    (∀ x : activeCarrier A C α,
      q.base x = activeSourcePart A C α x) := by
  constructor
  · rintro ⟨g, hg⟩ x
    calc
      q.base x = E.part (q.embedding x) := (q.projects x).symm
      _ = E.part (g.toEmbedding x) := by rw [hg]
      _ = activeSourcePart A C α x := g.map_part x
  · intro h
    refine ⟨{ toEmbedding := q.embedding, map_part := ?_ }, rfl⟩
    intro x
    exact (q.projects x).trans (h x)

/-- Two distinct vertices sharing an actual A-part obstruct using any
selected-copy base embedding as a partite gluing map for the FULL source:
the selected base embedding is injective, while the part map is not. -/
theorem selectedCopy_notPartiteGluing_of_partCollision
    (family : Set (Embedding Source D))
    (q : DesignatedCopy Source D E family)
    (x y : activeCarrier A C α)
    (hxy : x ≠ y)
    (hPart : activeSourcePart A C α x =
      activeSourcePart A C α y) :
    ¬ ∃ g : StructuralRamsey.Partite.Embedding
      (actualActiveSubsystemPartite A C α) E,
      g.toEmbedding = q.embedding := by
  intro h
  have hBase :=
    (selectedCopy_isPartiteGluing_iff_basePart
      A C α E D family q).mp h
  have hEq : q.base x = q.base y :=
    (hBase x).trans (hPart.trans (hBase y).symm)
  exact hxy (q.base.injective hEq)

/-- Nontriviality of the actual projected A-fibre gives a genuine
collision in the canonical active A-part map, independently of the
selected family and all future witness geometry. -/
theorem activePart_collision_of_distinct_projected_carriers
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hDifferent : copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ x y : activeCarrier A C α, x ≠ y ∧
      activeSourcePart A C α x = activeSourcePart A C α y := by
  classical
  have hPoint : ∃ u : UA, a.val u ≠ b.val u := by
    by_contra hNo
    push Not at hNo
    have hEmb : a.val = b.val := Embedding.ext (fun u => hNo u)
    exact hDifferent (congrArg copyCarrier hEmb)
  obtain ⟨u, hDiff⟩ := hPoint
  let x : activeCarrier A C α :=
    ⟨a.val u, projected_mem_activeCarrier A C α a u⟩
  let y : activeCarrier A C α :=
    ⟨b.val u, projected_mem_activeCarrier A C α b u⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    exact hDiff (congrArg Subtype.val h)
  · apply α.injective
    calc
      α (activeSourcePart A C α x) = C.part x.val :=
        activeSourcePart_spec A C α x
      _ = α u := a.property u
      _ = C.part y.val := (b.property u).symm
      _ = α (activeSourcePart A C α y) :=
        (activeSourcePart_spec A C α y).symm

/-- The precise no-go for the tempting canonical-index shortcut:
two physically distinct projected A-copies in the active fibre prevent
every selected full-active-target copy from being a partite gluing
embedding with its original selected relational embedding. -/
theorem selectedCopy_notPartiteGluing_of_nontrivialActive
    (family : Set (Embedding Source D))
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hDifferent : copyCarrier a.val ≠ copyCarrier b.val)
    (q : DesignatedCopy Source D E family) :
    ¬ ∃ g : StructuralRamsey.Partite.Embedding
      (actualActiveSubsystemPartite A C α) E,
      g.toEmbedding = q.embedding := by
  obtain ⟨x, y, hxy, hPart⟩ :=
    activePart_collision_of_distinct_projected_carriers
      A C α a b hDifferent
  exact selectedCopy_notPartiteGluing_of_partCollision
    A C α E D family q x y hxy hPart

end Criterion

end StructuralRamsey.Girth
