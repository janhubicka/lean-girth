import Girth.CompletionBudget

/-! # Finite image of selected standard-picture indices

The circulation proof begins with a finite tested family, then assigns to
each tested member some standard picture containing it. Only the pictures
actually selected should be used as vertices of the outer join tree.

The image of an arbitrary assignment from a finite tested family is finite,
and the induced assignment onto that image is surjective. This packages
those elementary facts so the finite-completion cardinal budget can be
applied without assuming surjectivity of the original choices.
-/

namespace StructuralRamsey.Girth

universe v
variable {N I : Type v}

/-- The standard-picture indices actually used by the tested family. -/
def OwnerImage (choice : N → I) : Type v :=
  Set.range choice

namespace OwnerImage

/-- Every tested label maps to its selected standard-picture index in the
image type. -/
def owner (choice : N → I) : N → OwnerImage choice :=
  fun n => ⟨choice n, ⟨n, rfl⟩⟩

/-- The chosen-image assignment is surjective, even if the original choice
map had a much larger codomain. -/
theorem owner_surjective (choice : N → I) :
    Function.Surjective (owner choice) := by
  rintro ⟨i, ⟨n, hni⟩⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hni

/-- Recover the original standard-copy choice after passing to the image. -/
theorem val_owner (choice : N → I) (n : N) :
    (owner choice n).1 = choice n := rfl

/-- Finiteness of the chosen owner image, with no finiteness assumption on
the collection of all possible standard pictures. -/
noncomputable def fintype [Fintype N] (choice : N → I) :
    Fintype (OwnerImage choice) := by
  haveI : Finite (OwnerImage choice) :=
    Finite.of_surjective (owner choice) (owner_surjective choice)
  exact Fintype.ofFinite (OwnerImage choice)

/-- A nonempty tested family has at least one selected standard picture. -/
theorem nonempty [Nonempty N] (choice : N → I) :
    Nonempty (OwnerImage choice) :=
  Nonempty.map (owner choice) inferInstance

/-- There are no more distinct selected standard pictures than selected
members. -/
theorem card_le [Fintype N] (choice : N → I) :
    letI : Fintype (OwnerImage choice) := fintype choice
    Fintype.card (OwnerImage choice) ≤ Fintype.card N := by
  classical
  letI : Fintype (OwnerImage choice) := fintype choice
  exact Fintype.card_le_of_surjective
    (owner choice) (owner_surjective choice)

end OwnerImage

end StructuralRamsey.Girth
