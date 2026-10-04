import Girth.DesignatedPicture
import PartiteConstruction.Partite.InducedInitial

/-! # Designated-copy base case

The initial picture is a disjoint union of one B-copy for each member of the
base Ramsey family.  These component copies are exactly the designated copies
needed by the main girth induction, and every irreducible lies in one of them.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {VB P I : Type v}

/-- Canonical designated component of the initial picture. -/
def initialDesignatedCopy
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (β : I → RelStructure.Embedding B D)
    (i : I) :
    DesignatedCopy B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun j => (β j).toFunctionEmbedding))
      (Set.range β) where
  base := β i
  base_mem := ⟨i, rfl⟩
  lift := {
    val := StructuralRamsey.Partite.Initial.copyEmbedding B
      (fun j => (β j).toFunctionEmbedding) i
    property := by
      intro b
      exact StructuralRamsey.Partite.Initial.copy_part B
        (fun j => (β j).toFunctionEmbedding) i b
  }

/-- The initial disjoint-union picture satisfies actual designated-copy
irreducible coverage. -/
theorem initial_designatedCoversIrreducibles
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (β : I → RelStructure.Embedding B D)
    [Nonempty I] :
    DesignatedCoversIrreducibles B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun j => (β j).toFunctionEmbedding))
      (Set.range β) := by
  intro T hT
  obtain ⟨i, hi⟩ :=
    StructuralRamsey.Partite.Induced.Initial.irreducible_same_index
      B (fun j => (β j).toFunctionEmbedding) T hT
  refine ⟨initialDesignatedCopy B D β i, ?_⟩
  intro z
  refine ⟨z.1.2, ?_⟩
  change z.1 =
    StructuralRamsey.Partite.Initial.copyEmbedding B
      (fun j => (β j).toFunctionEmbedding) i z.1.2
  apply Prod.ext
  · exact hi z
  · rfl

end StructuralRamsey.Girth
