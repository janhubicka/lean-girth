import Girth.TrainSelectedMixedCoreAttachment
import Girth.TrainRecursiveSelectedLowerActualInputs
import Girth.TrainRecursiveActivePartite

set_option autoImplicit false
set_option Elab.async false

/-!
# The genuine selected lower ForestTailStage has MIXED core coverage

The same-q=2 local F_t witness must NOT supply the generally false
property that all irreducibles of its core extend to A.

It already supplies the correct property in its checked
ForestTailStage.mixedCoverage field: every core irreducible lies in
a selected copy of the ENTIRE local active target, or in an ambient
physical A-copy.

The selected gluing index subtype is exactly the lower selected
designated-copy subtype. Coarsening and relabelling part maps
change no underlying relational embedding, so the checked selected
copy is literally the same physical gluing image. No disjoint
sum of copies, support-edge pruning or index quotient is used.

This supplies the local hypothesis of the generic nested mixed
coverage transfer in TrainSelectedMixedCoreAttachment, and hence
the output's original selected B-or-A coverage without a core
IrreduciblesExtendTo A premise. In particular this remains valid
at q=2, conditional only on a real lower F_t selected stage.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

/-- The actual selected lower ForestTailStage provides precisely the
local selected-target-or-A mixed coverage after A-part coarsening.
It is a direct application of the genuine lower mixedCoverage field,
not a fresh A-extension hypothesis. -/
theorem ForestTailStage.coarsenedSelected_localMixedCoverage
    {L : RelLanguage.{u}} {UA X V : Type v}
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA X)
    (Large : StructuralRamsey.Partite.System L UA V)
    {family : Set (Embedding Target.toRelStructure Large.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (lower : ForestTailStage A Target.toRelStructure
      Large.toRelStructure family t targetTrain
      (fun μ => Large.part ⁻¹' fineAllowed μ))
    (hFamilyParts : ∀ b, b ∈ family →
      ∀ x : X, Large.part (b x) = Target.part x) :
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure lower.system family // b ∈ lower.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large lower.system lower.isPartite family
        hFamilyParts lower.selected i
    ∀ (T : Set lower.Vertex),
      (E.toRelStructure.induce T).Irreducible →
        (∃ i : I, ∀ z : T,
          ∃ x : X, z.1 = (f i).toEmbedding x) ∨
        (∃ a : Embedding A E.toRelStructure,
          ∀ z : T, ∃ u : UA, z.1 = a u) := by
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure lower.system family // b ∈ lower.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite family
      hFamilyParts lower.selected i
  dsimp only
  intro T hT
  have hOld : (lower.system.toRelStructure.induce T).Irreducible :=
    hT
  rcases lower.mixedCoverage T hOld with
    ⟨q, hSelected, hq⟩ | ⟨a, ha⟩
  · left
    refine ⟨⟨q, hSelected⟩, ?_⟩
    intro z
    obtain ⟨x, hx⟩ := hq z
    refine ⟨x, ?_⟩
    exact hx
  · right
    exact ⟨a, ha⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
