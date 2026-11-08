import Girth.TrainRecursiveNontrivialActiveCoverage
import Girth.TrainRecursiveSelectedLowerActualInputs

set_option autoImplicit false
set_option Elab.async false

/-!
# Seven selected lower-stage inputs from the actual nontrivial ordered fibre

The genuinely nontrivial branch of the ordered finite picture pass supplies
two projected A-copies with different PHYSICAL carriers. This is enough
to discharge nonempty active support, rather than demanding a separate
chosen point or replacing the exact active subsystem by a larger part fibre.

Combining the checked high-girth active A-coverage theorem with the actual
selected lower-stage input bundle gives all seven geometry/arrow clauses
for the exact old active source. Same-copy rigidity comes from the ordered A
and is not another assumption.

This lemma remains conditional on an actual selected lower ForestTailStage,
its DesignatedArrow, and part-preserving embeddings over a large A-partite
base. In particular it does NOT construct a local PictureStep, global
gluing FullSystemGirthGT, or attached-output SupremeCycleBound.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P Q : Type v}

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
local notation "A" => A₀.ordered

/-- The seven genuine selected lower-stage inputs follow from the old
ordered stage and the actual nontrivial projected fibre, without extra
active-carrier nonemptiness, same-copy rigidity, or target A-coverage. -/
theorem ForestTailStage.orderedTrueActiveSelected_localInputBundle_of_nontrivial
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
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A) Target E κ := by
  have hCoverage : IrreduciblesExtendTo A
      (actualActiveSubsystemPartite A old.system
        e.toFunctionEmbedding).toRelStructure :=
    old.orderedTrueActive_irreduciblesExtendTo_of_nontrivial
      A₀ hBaseLinear hBaseStrong e hPair hHigh
  exact ForestTailStage.coarsenedSelected_actualLocalInputBundle
    A (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding)
    large lowerFamily fineAllowed lower hLarge hCoverage
    hFamilyParts q hq κ hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
