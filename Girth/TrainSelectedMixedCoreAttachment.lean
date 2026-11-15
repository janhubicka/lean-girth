import Girth.ForestSelectedMixedCoverage
import Girth.TrainRecursiveSelectedLowerActualInputs
import Girth.AttachmentGeometry

set_option autoImplicit false
set_option Elab.async false

/-!
# Preserve mixed irreducible coverage using a genuine selected local core

At head cutoff q=2 the generic FreeAttachment constructor's demand
that EVERY core irreducible extend to A can be mathematically
impossible while retaining A-strong selected target copies.
The actual finite F_t witness supplies a weaker and appropriate
local invariant: each core irreducible is contained in one literal
selected gluing copy of the COMPLETE old active target, OR in one
ambient A-copy of the core.

Given old selected B-or-A irreducible coverage, these two nested
mixed covers suffice for the assembled output's SELECTED B-or-A
irreducible coverage:

* an irreducible in an old standard is handled by old coverage;
* an irreducible in the core A alternative stays an ambient A-copy;
* an irreducible in the core selected gluing copy is reflected back
  to the genuine induced active old source, then old coverage picks
  an ORIGINAL selected B-copy or A-copy, transported in that same
  standard. The actual designated source label is unchanged.

This bypasses the q=2 IrreduciblesExtendTo A E coreCoverage field
without weakening the FINAL output mixed coverage. It does not yet
construct the replacement q=2 ForestTailStage: the other necessary
core support and picture fields must be combined separately.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- A free attachment preserves selected B-or-A coverage even when
the local core has only SELECTED ACTIVE-TARGET-or-A coverage, rather
than the false stronger assertion that every core irreducible lies
in an ambient A-copy. The local designated copies are the EXACT
gluing family used to attach the full old standards. -/
theorem selectedBorACoversIrreducibles_partiteAttachment_of_mixedCore
    {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : SelectedBorACoversIrreducibles A B D C family selected)
    (hLocal :
      ∀ (T : Set Y), (E.toRelStructure.induce T).Irreducible →
        (∃ i : I, ∀ z : T, ∃ s : S, z.1 = (f i).toEmbedding s) ∨
        (∃ a : Embedding A E.toRelStructure,
          ∀ z : T, ∃ u : UA, z.1 = a u)) :
    SelectedBorACoversIrreducibles A B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family
      (transportedSelectedCopies B D C family selected S E f) := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let core : Embedding E.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  let copy (i : I) : Embedding C.toRelStructure Whole :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  intro T hT
  let incT : Embedding (Whole.induce T) Whole :=
    RelStructure.inclusion Whole T
  have hSplit :=
    RelStructure.Attachment.irreducible_core_or_copy
      (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
      (f := fun i => (f i).toEmbedding) T hT
  rcases hSplit with hCore | ⟨i, hCopy⟩
  · have hCoreRange : ∀ z : T, ∃ y : Y, incT z = core y := by
      intro z
      exact hCore z
    let eE : Embedding (Whole.induce T) E.toRelStructure :=
      incT.factorThroughRange core hCoreRange
    have hEIrreducible :
        (E.toRelStructure.induce (Set.range eE)).Irreducible :=
      hT.range_embedding eE
    rcases hLocal (Set.range eE) hEIrreducible with
      ⟨j, hSelectedCore⟩ | ⟨a, hCoveredA⟩
    · have hIntoGluing : ∀ z : T, ∃ s : S,
          eE z = (f j).toEmbedding s := by
        intro z
        exact hSelectedCore ⟨eE z, ⟨z, rfl⟩⟩
      let eS : Embedding (Whole.induce T)
          (C.toRelStructure.induce S) :=
        eE.factorThroughRange (f j).toEmbedding hIntoGluing
      let inclusion : Embedding
          (C.toRelStructure.induce S) C.toRelStructure :=
        RelStructure.inclusion C.toRelStructure S
      let eOld : Embedding (Whole.induce T) C.toRelStructure :=
        inclusion.comp eS
      have hOldIrreducible :
          (C.toRelStructure.induce (Set.range eOld)).Irreducible :=
        hT.range_embedding eOld
      have hGlue (z : T) :
          core ((f j).toEmbedding (eS z)) =
            copy j (eOld z) := by
        exact attachment_core_gluing_eq_standard
          C.toRelStructure S E.toRelStructure
          (fun i => (f i).toEmbedding) j (eS z)
      rcases hOld (Set.range eOld) hOldIrreducible with
        ⟨q, hSelectedQ, hOldQ⟩ | ⟨aOld, hOldA⟩
      · left
        refine ⟨q.transportToStandard f j,
          ⟨j, q, hSelectedQ, rfl⟩, ?_⟩
        intro z
        obtain ⟨b, hb⟩ :=
          hOldQ ⟨eOld z, ⟨z, rfl⟩⟩
        refine ⟨b, ?_⟩
        calc
          z.1 = core (eE z) :=
            Classical.choose_spec (hCoreRange z)
          _ = core ((f j).toEmbedding (eS z)) :=
            congrArg core (Classical.choose_spec (hIntoGluing z))
          _ = copy j (eOld z) := hGlue z
          _ = copy j (q.embedding b) := congrArg (copy j) hb
      · right
        refine ⟨(copy j).comp aOld, ?_⟩
        intro z
        obtain ⟨u, hu⟩ :=
          hOldA ⟨eOld z, ⟨z, rfl⟩⟩
        refine ⟨u, ?_⟩
        calc
          z.1 = core (eE z) :=
            Classical.choose_spec (hCoreRange z)
          _ = core ((f j).toEmbedding (eS z)) :=
            congrArg core (Classical.choose_spec (hIntoGluing z))
          _ = copy j (eOld z) := hGlue z
          _ = copy j (aOld u) := congrArg (copy j) hu
    · right
      refine ⟨core.comp a, ?_⟩
      intro z
      obtain ⟨u, hu⟩ :=
        hCoveredA ⟨eE z, ⟨z, rfl⟩⟩
      refine ⟨u, ?_⟩
      calc
        z.1 = core (eE z) :=
          Classical.choose_spec (hCoreRange z)
        _ = core (a u) := congrArg core hu
  · have hCopyRange : ∀ z : T, ∃ x : X, incT z = copy i x := by
      intro z
      exact hCopy z
    let eC : Embedding (Whole.induce T) C.toRelStructure :=
      incT.factorThroughRange (copy i) hCopyRange
    have hOldIrreducible :
        (C.toRelStructure.induce (Set.range eC)).Irreducible :=
      hT.range_embedding eC
    rcases hOld (Set.range eC) hOldIrreducible with
      ⟨q, hSelectedQ, hq⟩ | ⟨a, ha⟩
    · left
      refine ⟨q.transportToStandard f i,
        ⟨i, q, hSelectedQ, rfl⟩, ?_⟩
      intro z
      obtain ⟨b, hb⟩ :=
        hq ⟨eC z, ⟨z, rfl⟩⟩
      refine ⟨b, ?_⟩
      calc
        z.1 = copy i (eC z) :=
          Classical.choose_spec (hCopyRange z)
        _ = copy i (q.embedding b) := congrArg (copy i) hb
    · right
      refine ⟨(copy i).comp a, ?_⟩
      intro z
      obtain ⟨u, hu⟩ := ha ⟨eC z, ⟨z, rfl⟩⟩
      refine ⟨u, ?_⟩
      calc
        z.1 = copy i (eC z) :=
          Classical.choose_spec (hCopyRange z)
        _ = copy i (a u) := congrArg (copy i) hu

end StructuralRamsey.Girth
