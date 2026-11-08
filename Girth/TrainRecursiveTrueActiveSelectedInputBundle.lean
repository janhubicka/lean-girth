import Girth.TrainRecursiveSelectedLowerActualInputs
import Girth.TrainRecursiveTrueActiveCoverage

set_option autoImplicit false
set_option Elab.async false

/-!
# Seven selected local fine-witness inputs for the GENUINE active lower source

The true active target is the induced subsystem on the original physical
active carrier, not the union of ambient part fibres. At old bottom
cutoff at least three, the already audited true-active coverage theorem
proves its irreducible A-extension. The lower selected ForestTailStage
then provides seven exact inputs to the nontrivial attachment: partiteness,
irreducible A-coverage, injective selected physical labels, bottom
mixed forest, restriction of the complete fine train, adjacent fine
parameters and the true partite family Ramsey arrow.

Only the actual lower stage and its DesignatedArrow are assumed.
The large base must genuinely be A-partite and its designated
embeddings must preserve A-parts. This is a conditional geometry
interface: it does not construct the lower finite Ramsey pass,
output SupremeCycleBound, or any Hales--Jewett-power girth.
No appendix/manuscript modifications.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB P Q : Type v}

/-- All seven exact selected local inputs follow at once when the lower
stage is built over the ACTUAL old active source. In particular,
irreducible A-coverage of that source is DERIVED from the old stage,
rather than added as an independent geometric assumption. -/
theorem ForestTailStage.trueActiveSelected_localInputBundle
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L P}
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (old : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (large : StructuralRamsey.Partite.System L UA Q)
    {lowerFamily : Set (Embedding
      (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding).toRelStructure
      large.toRelStructure)}
    {lowerCuts : List ℕ}
    {lowerTrain : EdgeTrainLevels
      (OldACarrierEdge A
        (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding).toRelStructure)
      lowerCuts.length}
    (fineAllowed : Fin (lowerCuts.length + 1) → Set UA)
    (lower : ForestTailStage A
      (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding).toRelStructure
      large.toRelStructure lowerFamily lowerCuts lowerTrain
      (fun ν => large.part ⁻¹' fineAllowed ν))
    (hA : A.Irreducible)
    (hBaseLinear : ALinear A D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base))
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A old.system e.toFunctionEmbedding).Nonempty)
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding)
    (hHigh : 3 ≤ t.headD 0)
    (hLarge : large.IsPartiteOver A)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
        large.part (b x) =
        (actualActiveSubsystemPartite A old.system e.toFunctionEmbedding).part x)
    (q : ℕ) (hq : q ≤ lowerCuts.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow lower κ) :
    let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
    let E := lower.system.coarsenVia large lower.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure large.toRelStructure lower.system lowerFamily //
      b ∈ lower.selected}
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
  let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  have hTargetCoverage : IrreduciblesExtendTo A Target.toRelStructure :=
    old.trueActive_irreduciblesExtendTo hA hBaseLinear
      hBaseStrong e hRigid hActive projected hHigh
  exact ForestTailStage.coarsenedSelected_actualLocalInputBundle
    A Target large lowerFamily fineAllowed lower hLarge
    hTargetCoverage hFamilyParts q hq κ hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
