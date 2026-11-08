import Girth.TrainRecursiveCoarsenedSelectedFamilyArrow
import Girth.TrainRecursiveSelectedLowerActualInputs

set_option autoImplicit false
set_option Elab.async false

/-!
# The complete selected lower fine-input bundle with an INDEXED Ramsey arrow

The seven-field coarsenedSelected_actualLocalInputBundle is already checked
on main, but its ordinary Partite.Arrow field forgets which selected
designated copy was monochromatic. The actual first-wagon refining
PictureStep requires a chosen index i of the LITERAL selected-copy subtype,
with the specific prescribed partite embedding f i monochromatic.

The strengthened selectedFamilyArrow_after_largeBaseCoarsen retains that
index. This module combines the six pre-existing geometric fields with the
indexed arrow into a single exact fine-witness interface. It does NOT
assume the indexed arrow as an additional premise, infer a lower Ramsey
stage from an initial Hales--Jewett arrow, or derive output SupremeCycleBound.

The actual selected lower ForestTailStage, its DesignatedArrow and genuine
part-preserving family over a large A-partite base remain explicit.
No source edge, ambient physical A-support edge, part, or wagon label is
deleted or coalesced. Circulation only; no appendix/TeX marker updates.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Six intrinsic selected lower geometry fields PLUS the precise
selected-index partite family arrow needed to apply the existing
refiningPictureStep_of_fineWitness. No new mathematical assumptions
relative to coarsenedSelected_actualLocalInputBundle. -/
theorem ForestTailStage.coarsenedSelected_actualIndexedLocalInputBundle
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (D : StructuralRamsey.Partite.System L UA P)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (S : ForestTailStage A Target.toRelStructure D.toRelStructure
      family t targetTrain
      (fun ν => D.part ⁻¹' fineAllowed ν))
    (hD : D.IsPartiteOver A)
    (hTargetCoverage : IrreduciblesExtendTo A Target.toRelStructure)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (q : ℕ) (hq : q ≤ t.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow S κ) :
    let E := S.system.coarsenVia D S.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure D.toRelStructure S.system family //
        b ∈ S.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target D S.system S.isPartite family hFamilyParts
        S.selected i
    E.IsPartiteOver A ∧
      IrreduciblesExtendTo A E.toRelStructure ∧
      Function.Injective (fun i : I =>
        bSupportPiece A ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A
          (fun i : I => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (t.length + 1)) (i : I)
        (a b : Embedding A Target.toRelStructure),
        S.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        targetTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      S.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      (∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) E → κ,
        ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A) Target,
          χ ((f i).comp a) = χ ((f i).comp b)) := by
  have hBasics := S.coarsenedSelected_actualLocalInputBundle
    A Target D family fineAllowed hD hTargetCoverage
    hFamilyParts q hq κ hArrow
  rcases hBasics with
    ⟨hPartite, hCoverage, hInjective, hForest,
      hRestriction, hParameters, _hUnindexed⟩
  refine ⟨hPartite, hCoverage, hInjective, hForest,
    hRestriction, hParameters, ?_⟩
  exact S.selectedFamilyArrow_after_largeBaseCoarsen
    A Target D family hFamilyParts κ hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
