import Girth.ForestActualACopyOwner
import Girth.LocalForestBridge

/-!
# Excluding new core B-copies without covering every local A-edge

The nonpruning mixed forest increment permits ambient A-edges of the
local witness which belong to no designated gluing copy.  Consequently
the existing actual B-copy ownership theorem has the unavailable
hypothesis LocalIrreduciblesCoveredByAInCopies at these recursive steps.

That hypothesis is unnecessary for the nontrivial source target B.
Assume every irreducible in the local core E extends to A, as
guaranteed by the high-girth A-decoration, and that B is irreducible
and cannot embed into A (because it has more than one A-edge).

Then B cannot embed into E: such a copy would lie inside a local A,
giving B -> A. In a free relational attachment every irreducible
copy lies either in the core or in one standard picture; the core
case is excluded. Hence every attached B-copy factors through a
standard picture without covering all local edges.

This does NOT establish coverage of every smaller irreducible
A-substructure by designated B-copies: the standing picture
invariant must be weakened or separately repaired.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Old Core I : Type v}

/-- If every irreducible in E extends to A, no irreducible
B can embed into E unless it embeds into A itself. -/
theorem no_core_B_of_irreduciblesExtendTo
    (A : RelStructure L UA) (B : RelStructure L VB)
    (hB : B.Irreducible)
    (E : RelStructure L Core)
    (hExtend : RelStructure.IrreduciblesExtendTo A E)
    (hNoBA : ¬ Nonempty (RelStructure.Embedding B A)) :
    ¬ Nonempty (RelStructure.Embedding B E) := by
  rintro ⟨b⟩
  let T : Set Core := copyCarrier b
  have hIrr : (E.induce T).Irreducible :=
    hB.range_embedding b
  obtain ⟨a, hCovered⟩ := hExtend T hIrr
  have hFactor : ∀ x : VB, ∃ z : UA, b x = a z := by
    intro x
    obtain ⟨z, hz⟩ := hCovered ⟨b x, ⟨x, rfl⟩⟩
    exact ⟨z, hz⟩
  let embedBA : RelStructure.Embedding B A :=
    b.factorThroughRange a hFactor
  exact hNoBA ⟨embedBA⟩

/-- Every actual irreducible B-copy in an attached picture belongs
to a full standard picture, with no coverage hypothesis for its
local core A-edges. -/
theorem attached_bCopy_standard_of_noCoreB
    (A : RelStructure L UA)
    (B : RelStructure L VB) (hB : B.Irreducible)
    (OldPicture : RelStructure L Old)
    (S : Set Old)
    (E : RelStructure L Core)
    (f : I → RelStructure.Embedding (OldPicture.induce S) E)
    (hExtend : RelStructure.IrreduciblesExtendTo A E)
    (hNoBA : ¬ Nonempty (RelStructure.Embedding B A))
    (b : RelStructure.Embedding B
      (RelStructure.Attachment.attach OldPicture S E f)) :
    ∃ i : I, ∀ u : VB, ∃ x : Old,
      b u = (RelStructure.Attachment.copyEmbedding
        OldPicture S E f i) x := by
  rcases attachment_aCopy_core_or_standard
      B hB OldPicture S E f b with hCore | hStandard
  · let core : RelStructure.Embedding E
        (RelStructure.Attachment.attach OldPicture S E f) :=
      RelStructure.Attachment.coreEmbedding OldPicture S E f
    let bE : RelStructure.Embedding B E :=
      b.factorThroughRange core hCore
    exact False.elim
      ((no_core_B_of_irreduciblesExtendTo A B hB E
        hExtend hNoBA) ⟨bE⟩)
  · exact hStandard

end StructuralRamsey.Girth
