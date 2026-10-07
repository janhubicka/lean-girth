import Girth.ForestAuxiliaryDeletion
import Girth.MixedForest

/-! # Removing auxiliary A-copies from a mixed A/B forest

The circulation completion proof glues local forests containing both
designated B-copies and temporary A-copies used as connectors.  Since an
A-member's A-support is precisely one edge, all the temporary A-members can be
removed at once, while retaining any specified original A- or B-members.

The result depends on the one-edge deletion theorem, not on the false
assertion that every subfamily of a forest remains a forest.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι : Type v}

/-- An A-member of a mixed A/B family has a one-edge support piece. -/
theorem ABMember.a_supportPiece_isOneEdge
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (R : RelStructure L W)
    (a : Embedding A R) :
    ((ABMember.a a : ABMember A B R).supportPiece A).IsOneEdge :=
  rfl

/-- Deleting all non-retained A-members from a mixed support forest preserves
the forest property.  The remaining family can contain both originally
selected A-members and designated B-members. -/
theorem ForestOfCopies.restrict_mixed_of_auxiliary_A
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (R : RelStructure L W)
    [Fintype ι]
    (family : ι → ABMember A B R)
    (hForest :
      ForestOfCopies (fun i : ι => (family i).supportPiece A))
    (keep : Finset ι)
    (hAuxiliary :
      ∀ i : ι, i ∉ keep →
        ∃ a : Embedding A R, family i = ABMember.a a) :
    ForestOfCopies
      (fun i : {i : ι // i ∈ keep} =>
        (family i.1).supportPiece A) := by
  apply hForest.restrict_of_oneEdge_outside keep
  intro i hi
  obtain ⟨a, ha⟩ := hAuxiliary i hi
  rw [ha]
  exact ABMember.a_supportPiece_isOneEdge A B R a

end StructuralRamsey.Girth
