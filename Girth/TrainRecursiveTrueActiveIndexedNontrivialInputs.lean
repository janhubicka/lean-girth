import Girth.TrainRecursiveOrderedNontrivialSelectedInputs
import Girth.TrainRecursiveCoarsenedSelectedIndexedBundle
import Girth.TrainRecursiveTrueActiveTwoCopies

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact nontrivial-fibre geometry with the actual indexed selected Ramsey arrow

The genuine nontrivial physical projected fibre provides two distinct
A-copies of the true active target. Ordered source rigidity and the old
stage's mixed coverage provide irreducible A-coverage of that target.
A REAL selected lower ForestTailStage, its DesignatedArrow and actual
part-preserving large-base family then provide all six local geometry
certificates PLUS an indexed selected partite family arrow.

Unlike the formerly checked unindexed bundle, the result retains the
actual designated gluing index i; it matches the hArrow interface in
refiningPictureStep_of_fineWitness. No arbitrary selected output is
postulated. This still does not build the lower stage, supply its full
gluing-system girth or prove the attached output SupremeCycleBound.
Circulation only, no appendix or TeX changes.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Q : Type v}
variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
local notation "A" => A₀.ordered

/-- The precise two-copy and seven-field INDEXED fine-witness bundle
on the complete true active target, using one genuinely selected lower
ForestTailStage and no independent target-coverage or arrow hypothesis. -/
theorem ForestTailStage.orderedTrueActiveSelected_indexedInputAndTwoCopies_of_nontrivial
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (old : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (large : StructuralRamsey.Partite.System L.withOrder UA Q)
    {lowerFamily : Set (Embedding
      (actualActiveSubsystemPartite A old.system
        e.toFunctionEmbedding).toRelStructure large.toRelStructure)}
    {lowerCuts : List ℕ}
    {lowerTrain : EdgeTrainLevels
      (OldACarrierEdge A (actualActiveSubsystemPartite A old.system
        e.toFunctionEmbedding).toRelStructure) lowerCuts.length}
    (fineAllowed : Fin (lowerCuts.length + 1) → Set UA)
    (lower : ForestTailStage A
      (actualActiveSubsystemPartite A old.system
        e.toFunctionEmbedding).toRelStructure
      large.toRelStructure lowerFamily lowerCuts lowerTrain
      (fun ν => large.part ⁻¹' fineAllowed ν))
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base))
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hHigh : 3 ≤ t.headD 0)
    (hLarge : large.IsPartiteOver A)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
        large.part (b x) =
          (actualActiveSubsystemPartite A old.system
            e.toFunctionEmbedding).part x)
    (q : ℕ) (hq : q ≤ lowerCuts.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow lower κ) :
    let Target := actualActiveSubsystemPartite A old.system
      e.toFunctionEmbedding
    let E := lower.system.coarsenVia large lower.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      large.toRelStructure lower.system lowerFamily // b ∈ lower.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target large lower.system lower.isPartite lowerFamily
        hFamilyParts lower.selected i
    (∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b) ∧
    E.IsPartiteOver A ∧
      IrreduciblesExtendTo A E.toRelStructure ∧
      Function.Injective (fun i : I =>
        bSupportPiece A ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A (fun i : I => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (lowerCuts.length + 1)) (i : I)
        (a b : Embedding A Target.toRelStructure),
        lower.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        lowerTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      lower.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      (∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) E → κ,
        ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) Target,
          χ ((f i).comp a) = χ ((f i).comp b)) := by
  let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  have hCoverage : IrreduciblesExtendTo A Target.toRelStructure :=
    old.orderedTrueActive_irreduciblesExtendTo_of_nontrivial
      A₀ hBaseLinear hBaseStrong e hPair hHigh
  have hTwo : ∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b :=
    activeTarget_twoGenuineCopies_of_nontrivialFibre
      A old.system e.toFunctionEmbedding hPair
  have hIndexed := lower.coarsenedSelected_actualIndexedLocalInputBundle
    A Target large lowerFamily fineAllowed hLarge hCoverage
    hFamilyParts q hq κ hArrow
  exact ⟨hTwo, hIndexed⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
