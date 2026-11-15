import Girth.TrainRealSelectedMixedCoreCoverage
import Girth.TrainRecursiveActivePartite

set_option autoImplicit false
set_option Elab.async false

/-!
# Real selected F_t lower stage -> original selected B-or-A output coverage

For a same-vector local F_t stage on the TRUE induced active source,
the lower selected ForestTailStage.mixedCoverage field covers every
irreducible core piece either by an actual SELECTED gluing image of
the entire active target or by one ambient physical A-copy.

Relabelling the lower coarsened A-parts along the processed old
A-projection changes no relational carrier or support edge. The
selected gluing index is the original literal selected lower-stage
copy label, and the underlying relational embedding is unchanged.

The generic nested mixed-core lemma then transports this coverage
through the actual free attachment. A core irreducible carried by
a gluing copy pulls back to the OLD true active target; old selected
B-or-A coverage supplies an ORIGINAL old B-copy or A-copy and
transporting that to the matching standard covers the core piece.
Thus the output's full selected mixed irreducible coverage is
preserved even at cutoff q=2, without requiring the impossible
IrreduciblesExtendTo A local core property.

This is the genuine mixedCoverage-field replacement for the q=2
attachment constructor. It does NOT yet build the remaining
ForestTailStage fields or a local Ramsey picture step.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

/-- The literal coarsened and relabelled selected F_t core has
sufficient mixed irreducible coverage to preserve the ORIGINAL
selected old B-or-A coverage after a free picture attachment.
Every selected index and physical support edge remains unchanged. -/
theorem ForestTailStage.actualAttachment_selectedMixedCoverage_of_localFt
    {L : RelLanguage.{u}} {UA VB P X V : Type v}
    (A : RelStructure L UA)
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (α : UA ↪ P)
    (Large : StructuralRamsey.Partite.System L UA V)
    {lowerFamily : Set (Embedding
      (C.toRelStructure.induce (activeCarrier A C α))
      Large.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A
        (C.toRelStructure.induce (activeCarrier A C α))) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (lower : ForestTailStage A
      (C.toRelStructure.induce (activeCarrier A C α))
      Large.toRelStructure lowerFamily t targetTrain
      (fun ν => Large.part ⁻¹' fineAllowed ν))
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A C α,
        Large.part (b x) =
          (actualActiveSubsystemPartite A C α).part x)
    (hOld : SelectedBorACoversIrreducibles
      A B D C family selected) :
    let S := activeCarrier A C α
    let Target := actualActiveSubsystemPartite A C α
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure lower.system lowerFamily //
        b ∈ lower.selected}
    let fSelected : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large lower.system lower.isPartite lowerFamily
        hFamilyParts lower.selected i
    let f : I → StructuralRamsey.Partite.Embedding
      (C.induce S) (E.relabel α) :=
      fun i => activePartiteToRelabelledCore
        A C α E (fSelected i)
    SelectedBorACoversIrreducibles A B D
      (StructuralRamsey.Partite.Attachment.attach C S
        (E.relabel α) f)
      family (transportedSelectedCopies
        B D C family selected S (E.relabel α) f) := by
  let S := activeCarrier A C α
  let Target := actualActiveSubsystemPartite A C α
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure lower.system lowerFamily //
      b ∈ lower.selected}
  let fSelected : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite lowerFamily
      hFamilyParts lower.selected i
  let f : I → StructuralRamsey.Partite.Embedding
      (C.induce S) (E.relabel α) :=
    fun i => activePartiteToRelabelledCore
      A C α E (fSelected i)
  have hLocal :
      ∀ (T : Set lower.Vertex),
        ((E.relabel α).toRelStructure.induce T).Irreducible →
        (∃ i : I, ∀ z : T,
          ∃ s : S, z.1 = (f i).toEmbedding s) ∨
        (∃ a : Embedding A (E.relabel α).toRelStructure,
          ∀ z : T, ∃ u : UA, z.1 = a u) := by
    exact lower.coarsenedSelected_localMixedCoverage
      A Target Large fineAllowed hFamilyParts
  exact selectedBorACoversIrreducibles_partiteAttachment_of_mixedCore
    A B D C family selected S (E.relabel α) f hOld hLocal

end StructuralRamsey.Girth.TrainRecursiveWitness
