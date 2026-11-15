import Girth.TrainRecursiveTrueActiveIndexedNontrivialInputs
import Girth.TrainRealSelectedFtSameVectorTrain
import Girth.TrainRealSelectedFtLocalBundle

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual same-vector F_t selected lower stage: all high-q local interfaces

For q>=3, the existing ordered true-active selected bundle proves
irreducible A-coverage of the TRUE active induced target, from the
actual OLD ForestTailStage and its genuine two-copy physical fibre.
This is essential: at q=2, A-partiteness and girth >2 alone do not
imply A-irreducible coverage (see Track 4 q2 obstruction note).

Once a real selected LOWER ForestTailStage is built over precisely
that induced active source and its LITERAL doubly-restricted old
train, the following are all supplied by checked existing lemmas:
* two genuine active physical A-copies;
* A-partite local core and irreducible A-extension;
* injective selected COMPLETE A-support;
* finite mixed SET forests through the SAME q;
* full original shared-edge train relation preservation/reflection,
  INCLUDING bottom and universal top;
* exact local adjacent part parameters;
* indexed PHYSICAL A-edge Ramsey family arrow;
* local positive FullSystemGirthGT at EVERY original tail cutoff.

This is a mathematical consolidation of the actual seven-field lower
bundle, the exact shared-edge train theorem and positive girth transfer.
No independent hRel, coreCoverage, positive-girth, physical-arrow or
selected-copy image injectivity oracle remains in this high-q LOCAL
interface. It does not construct the lower ForestTailStage or finish
the global F_t -> R_t finite pass. No q=2 coverage is asserted.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P V : Type v}
variable (A₀ : RelStructure L UA)
variable [LinearOrder UA] [Finite UA] [Nonempty UA]
local notation "A" => A₀.ordered

/-- All complete local F_t inputs for a genuine q>=3 physical
nontrivial selected lower stage at the SAME vector, including
full shared-edge relation reflection at each actual old cut and
the local exact positive full-system bounds. -/
theorem ForestTailStage.orderedTrueActive_sameVectorFt_complete_highCut
    {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D)
    (Large : StructuralRamsey.Partite.System L.withOrder UA V)
    {lowerFamily : Set (Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    (fineAllowed : Fin ((q :: tail).length + 1) → Set UA)
    (lower : ForestTailStage A
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily (q :: tail)
      (((old.train.restrict
        (sharedOldACarrierInclusion A old.system.toRelStructure
          (activeCarrier A old.system e.toFunctionEmbedding))).restrict
        (inducedACarrierToShared A old.system.toRelStructure
          (activeCarrier A old.system e.toFunctionEmbedding))))
      (fun ν => Large.part ⁻¹' fineAllowed ν))
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base))
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hHigh : 3 ≤ q)
    (hLarge : Large.IsPartiteOver A)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
        Large.part (b x) =
          (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding).part x)
    (κ : Type w) [Nonempty κ]
    (hLowerArrow : DesignatedArrow lower κ) :
    let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure Large.toRelStructure lower.system lowerFamily //
      b ∈ lower.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large lower.system lower.isPartite lowerFamily hFamilyParts
        lower.selected i
    (∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b) ∧
    E.IsPartiteOver A ∧
    IrreduciblesExtendTo A E.toRelStructure ∧
    Function.Injective (fun i : I => bSupportPiece A ((f i).toEmbedding)) ∧
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i : I => (f i).toEmbedding)) q ∧
    (∀ μ : Fin ((q :: tail).length + 1), ∀ i : I,
      ∀ p r : SharedOldACarrierEdge A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding),
      old.train.rel μ p.1 r.1 ↔
        lower.train.rel μ
          (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
            (activeCarrier A old.system e.toFunctionEmbedding)
            E.toRelStructure (fun j : I => (f j).toEmbedding) i p)
          (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
            (activeCarrier A old.system e.toFunctionEmbedding)
            E.toRelStructure (fun j : I => (f j).toEmbedding) i r)) ∧
    lower.train.AdjacentParameters (fun edge => edge.1)
      (fun μ => E.part ⁻¹' fineAllowed μ) ∧
    (∀ χ : OldACarrierEdge A E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A Target.toRelStructure,
        χ (actualEdge ((f i).toEmbedding.comp a)) =
          χ (actualEdge ((f i).toEmbedding.comp b))) ∧
    (∀ j : Fin (q :: tail).length, 0 < j.val →
      (activeGluingWitnessOrderOneData A old.system e.toFunctionEmbedding
        E.toRelStructure (fun i : I => (f i).toEmbedding)
        lower.train j.castSucc).FullSystemGirthGT ((q :: tail).get j)) := by
  let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy
    Target.toRelStructure Large.toRelStructure lower.system lowerFamily //
    b ∈ lower.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite lowerFamily hFamilyParts
      lower.selected i
  have hIndexed :=
    old.orderedTrueActiveSelected_indexedInputAndTwoCopies_of_nontrivial
      A₀ e Large fineAllowed lower hBaseLinear hBaseStrong hPair
      hHigh hLarge hFamilyParts q (by simp) κ hLowerArrow
  obtain ⟨hTwo, hPartite, hCoverage, hInjective, hMixed,
    _hTargetRestriction, hParameters, hIndexedArrow⟩ := hIndexed
  have hPhysicalArrow :=
    indexedPhysicalArrow_of_partiteFamilyArrow_for_orderedA
      A₀ Target E f
      (actualActiveSubsystemPartite_isPartiteOver
        A old.system D old.isPartite e)
      κ hIndexedArrow
  have hShared : ∀ μ : Fin ((q :: tail).length + 1), ∀ i : I,
      ∀ p r : SharedOldACarrierEdge A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding),
      old.train.rel μ p.1 r.1 ↔
        lower.train.rel μ
          (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
            (activeCarrier A old.system e.toFunctionEmbedding)
            E.toRelStructure (fun j : I => (f j).toEmbedding) i p)
          (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
            (activeCarrier A old.system e.toFunctionEmbedding)
            E.toRelStructure (fun j : I => (f j).toEmbedding) i r) := by
    exact lower.sameVectorSelected_oldSharedTrain_iff
      A old.system e.toFunctionEmbedding Large
      old.train fineAllowed hFamilyParts
  have hPositive : ∀ j : Fin (q :: tail).length, 0 < j.val →
      (activeGluingWitnessOrderOneData A old.system e.toFunctionEmbedding
        E.toRelStructure (fun i : I => (f i).toEmbedding)
        lower.train j.castSucc).FullSystemGirthGT ((q :: tail).get j) := by
    intro j hj
    exact lower.coarsenedSelected_fullSystem_at_positive
      A old.system e.toFunctionEmbedding Large hFamilyParts j hj
  exact ⟨hTwo, hPartite, hCoverage, hInjective, hMixed,
    hShared, hParameters, hPhysicalArrow, hPositive⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
