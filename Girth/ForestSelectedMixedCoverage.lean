import Girth.ForestMixedActiveGenerated

/-!
# Selected mixed irreducible coverage through an actual attachment

The recursive pass retains a selected subfamily of the prescribed projected
B-lifts.  Its coverage invariant must retain that membership: an arbitrary
projected lift with the same base is not necessarily selected.

This module preserves selected B-or-ambient-A irreducible coverage under the
actual free attachment.  The output selection consists precisely of the
literal transports of selected old copies to standards.  A core irreducible
is still absorbed by an ambient A-copy; no core edge is assigned to a
fictitious selected copy or discarded.

The active-generation wrapper then invokes the existing mixed-coverage
theorem using the family of selected base labels.  Accordingly it asks for
base strongness only for selected old copies.  Base A-linearity, honest
partite projection, ordered-source rigidity, and local core irreducible-to-A
extension remain explicit hypotheses.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Every irreducible lies in a selected B-copy or one ambient A-copy. -/
def SelectedBorACoversIrreducibles
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family)) : Prop :=
  ∀ (T : Set X), (C.toRelStructure.induce T).Irreducible →
    (∃ q : DesignatedCopy B D C family, q ∈ selected ∧
      ∀ z : T, ∃ b : VB, z.1 = q.embedding b) ∨
    (∃ a : RelStructure.Embedding A C.toRelStructure,
      ∀ z : T, ∃ u : UA, z.1 = a u)

/-- Forgetting selection gives the existing mixed-coverage invariant. -/
theorem SelectedBorACoversIrreducibles.forget
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {C : StructuralRamsey.Partite.System L P X}
    {family : Set (RelStructure.Embedding B D)}
    {selected : Set (DesignatedCopy B D C family)}
    (h : SelectedBorACoversIrreducibles A B D C family selected) :
    DesignatedBorACoversIrreducibles A B D C family := by
  intro T hT
  rcases h T hT with ⟨q, _, hq⟩ | hA
  · exact Or.inl ⟨q, hq⟩
  · exact Or.inr hA

/-- The literal selected copies in the output standards. -/
def transportedSelectedCopies
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E) :
    Set (DesignatedCopy B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family) :=
  {r | ∃ i : I, ∃ q : DesignatedCopy B D C family,
    q ∈ selected ∧ r = q.transportToStandard f i}

/-- Actual free attachment preserves selected mixed coverage.  The local
core clause concerns all irreducibles, not coverage by designated gluing
copies. -/
theorem selectedBorACoversIrreducibles_partiteAttachment
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hOld : SelectedBorACoversIrreducibles A B D C family selected)
    (hLocal : RelStructure.IrreduciblesExtendTo A E.toRelStructure) :
    SelectedBorACoversIrreducibles A B D
      (StructuralRamsey.Partite.Attachment.attach C S E f) family
      (transportedSelectedCopies B D C family selected S E f) := by
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
  · have hRange : ∀ z : T, ∃ y : Y, incT z = core y := by
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
  · have hRange : ∀ z : T, ∃ x : X, incT z = copy i x := by
      intro z
      exact hcopy z
    let eC : RelStructure.Embedding (Whole.induce T) C.toRelStructure :=
      incT.factorThroughRange (copy i) hRange
    have hIrr : (C.toRelStructure.induce (Set.range eC)).Irreducible :=
      hT.range_embedding eC
    rcases hOld (Set.range eC) hIrr with ⟨q, hSelected, hq⟩ | ⟨a, ha⟩
    · left
      refine ⟨q.transportToStandard f i, ⟨i, q, hSelected, rfl⟩, ?_⟩
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

/-- The existing active-generation theorem needs base strongness only for
the bases of the selected copies that witness mixed coverage. -/
theorem activeSubsystem_aGenerated_of_selectedMixedCoverage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (hA : A.Irreducible) (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A D)
    (hCover : SelectedBorACoversIrreducibles A B D C family selected)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family, q ∈ selected →
      AStrong A D (copyCarrier q.base))
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hActive : (activeCarrier A C e.toFunctionEmbedding).Nonempty) :
    AGenerated A
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) := by
  let selectedBases : Set (RelStructure.Embedding B D) :=
    {b | ∃ q : DesignatedCopy B D C family, q ∈ selected ∧ q.base = b}
  have hCover' : DesignatedBorACoversIrreducibles A B D C selectedBases := by
    intro T hT
    rcases hCover T hT with ⟨q, hSelected, hq⟩ | ha
    · left
      exact ⟨⟨q.base, ⟨q, hSelected, rfl⟩, q.lift⟩, hq⟩
    · exact Or.inr ha
  have hBaseStrong' : ∀ b : RelStructure.Embedding B D, b ∈ selectedBases →
      AStrong A D (copyCarrier b) := by
    intro b hb
    obtain ⟨q, hSelected, rfl⟩ := hb
    exact hBaseStrong q hSelected
  exact activeSubsystem_aGenerated_of_mixedCoverage A B D C selectedBases
    hA hPartite hLinear hCover' hBaseStrong' e hRigid hActive

end StructuralRamsey.Girth
