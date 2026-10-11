import Girth.DesignatedAttachment

/-!
# The correct nonpruning irreducible coverage invariant

The original circulation picture invariant required EVERY irreducible
to lie in a designated B-copy. This is too strong if the q>2 recursive
local witness contains A-support edges which are not in a designated
local gluing copy. Those A-edges should remain as legitimate
one-edge exceptional forest members: pruning would not be known to
preserve tail system-Girth.

Instead maintain MIXED coverage: every irreducible is contained
either in an actual designated B-copy or in one ambient A-copy.

This condition is preserved by the genuine free partite picture
attachment using ONLY the local core property
IrreduciblesExtendTo A E. An irreducible in the core is absorbed by
a core A-copy; one in a full standard picture is transported from
the old B-or-A coverage. There is no local edge coverage hypothesis.

For nontrivial B that cannot embed in A, mixed coverage still
guarantees every actual B-copy lies inside an actual designated
B-copy, because the A alternative cannot contain B. This retains
the geometric statement needed to track genuine B-pieces without
forcing uncovered A-edges into fictitious gluing B copies.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Every irreducible belongs to an ACTUAL designated B-copy
OR an ambient A-copy. The alternatives are physical copies. -/
def DesignatedBorACoversIrreducibles
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) : Prop :=
  ∀ (T : Set X), (C.toRelStructure.induce T).Irreducible →
    (∃ q : DesignatedCopy B D C family,
      ∀ z : T, ∃ b : VB, z.1 = q.embedding b) ∨
    (∃ a : RelStructure.Embedding A C.toRelStructure,
      ∀ z : T, ∃ u : UA, z.1 = a u)

/-- The physical designated-B-or-A irreducible cover is preserved
under the TRUE free partite attachment as soon as the local core
extends all its irreducibles to A. No local gluing edge coverage. -/
theorem designatedBorACoversIrreducibles_partiteAttachment
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : DesignatedBorACoversIrreducibles A B D C family)
    (hLocal : RelStructure.IrreduciblesExtendTo A E.toRelStructure) :
    DesignatedBorACoversIrreducibles A B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let core : RelStructure.Embedding E.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let copy (i : I) : RelStructure.Embedding C.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  intro T hT
  let incT : RelStructure.Embedding (Whole.induce T) Whole :=
    RelStructure.inclusion Whole T
  have hsplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding) T hT
  rcases hsplit with hcore | ⟨i, hcopy⟩
  · have hRange :
        ∀ z : T, ∃ y : Y, incT z = core y := by
      intro z
      exact hcore z
    let eE : RelStructure.Embedding (Whole.induce T) E.toRelStructure :=
      incT.factorThroughRange core hRange
    have hIrr : (E.toRelStructure.induce (Set.range eE)).Irreducible :=
      hT.range_embedding eE
    obtain ⟨a, hCovered⟩ := hLocal (Set.range eE) hIrr
    right
    refine ⟨core.comp a, ?_⟩
    intro z
    obtain ⟨u, hu⟩ := hCovered ⟨eE z, ⟨z, rfl⟩⟩
    refine ⟨u, ?_⟩
    calc
      z.1 = core (eE z) := Classical.choose_spec (hRange z)
      _ = core (a u) := congrArg core hu
  · have hRange :
        ∀ z : T, ∃ x : X, incT z = copy i x := by
      intro z
      exact hcopy z
    let eC : RelStructure.Embedding (Whole.induce T) C.toRelStructure :=
      incT.factorThroughRange (copy i) hRange
    have hIrr : (C.toRelStructure.induce (Set.range eC)).Irreducible :=
      hT.range_embedding eC
    rcases hOld (Set.range eC) hIrr with ⟨q, hq⟩ | ⟨a, ha⟩
    · left
      refine ⟨q.transportToStandard f i, ?_⟩
      intro z
      obtain ⟨b, hb⟩ := hq ⟨eC z, ⟨z, rfl⟩⟩
      refine ⟨b, ?_⟩
      calc
        z.1 = copy i (eC z) := Classical.choose_spec (hRange z)
        _ = copy i (q.embedding b) := congrArg (copy i) hb
    · right
      refine ⟨(copy i).comp a, ?_⟩
      intro z
      obtain ⟨u, hu⟩ := ha ⟨eC z, ⟨z, rfl⟩⟩
      refine ⟨u, ?_⟩
      calc
        z.1 = copy i (eC z) := Classical.choose_spec (hRange z)
        _ = copy i (a u) := congrArg (copy i) hu

/-- If B is irreducible and does not embed into A, MIXED coverage
still gives a genuine old designated B-owner for every actual B-copy. -/
theorem actualBCopy_designated_of_mixedCoverage
    (A : RelStructure L UA)
    (B : RelStructure L VB) (hB : B.Irreducible)
    [Finite VB]
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (hOld : DesignatedBorACoversIrreducibles A B D C family)
    (hNoBA : ¬ Nonempty (RelStructure.Embedding B A))
    (bOld : RelStructure.Embedding B C.toRelStructure) :
    ∃ q : DesignatedCopy B D C family, SameCopy bOld q.embedding := by
  classical
  let T : Set X := copyCarrier bOld
  have hIrr : (C.toRelStructure.induce T).Irreducible :=
    hB.range_embedding bOld
  rcases hOld T hIrr with ⟨q, hCovered⟩ | ⟨a, hCovered⟩
  · refine ⟨q, ?_⟩
    apply sameCopy_of_range_subset bOld q.embedding
    intro u
    exact hCovered ⟨bOld u, ⟨u, rfl⟩⟩
  · exfalso
    have hFactor : ∀ u : VB, ∃ x : UA,
        bOld u = a x := by
      intro u
      exact hCovered ⟨bOld u, ⟨u, rfl⟩⟩
    let bA : RelStructure.Embedding B A :=
      bOld.factorThroughRange a hFactor
    exact hNoBA ⟨bA⟩

end StructuralRamsey.Girth
