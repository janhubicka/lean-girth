import Girth.TrainRecursiveTrueActiveSelectedInputBundle
import Girth.ProjectedSupportCopy
import Girth.TrainRecursiveTrueActiveTwoCopies

set_option autoImplicit false
set_option Elab.async false

/-!
# Ordered true-active geometry without spurious irreducibility, rigidity
  or nonemptiness assumptions

For a genuinely finite ordered source A₀, its ordered expansion is
hereditarily irreducible and image-rigid: two ordered A-copies with equal
physical carrier are the same embedding. If the current base profile
has a projected A-copy, then the true active carrier is nonempty.
These three facts are automatically available at every nontrivial
ordered recursive step.

The previously verified generic true-active selected local-input bundle
can therefore be applied with no independent hA/hRigid/hActive
hypotheses. Only the natural A-linearity/selected-base-strongness,
actual lower stage and its designated arrow, A-partite larger base
and part-preserving family remain.

This is a conditional geometry theorem, not the local Ramsey step
or the attached-output SupremeCycleBound. Circulation only.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB P Q : Type v}

/-- For an ordered source, actual projected-copy existence already
discharges all THREE generic true-active target side conditions:
irreducibility, image rigidity and carrier nonemptiness. -/
theorem ForestTailStage.orderedTrueActiveSelected_localInputBundle
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family t targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (large : StructuralRamsey.Partite.System L.withOrder UA Q)
    {lowerFamily : Set (Embedding
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure large.toRelStructure)}
    {lowerCuts : List ℕ}
    {lowerTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure) lowerCuts.length}
    (fineAllowed : Fin (lowerCuts.length + 1) → Set UA)
    (lower : ForestTailStage A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure
      large.toRelStructure lowerFamily lowerCuts lowerTrain
      (fun ν => large.part ⁻¹' fineAllowed ν))
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A₀.ordered D (copyCarrier b.base))
    (projected : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding)
    (hHigh : 3 ≤ t.headD 0)
    (hLarge : large.IsPartiteOver A₀.ordered)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A₀.ordered old.system e.toFunctionEmbedding,
        large.part (b x) =
          (actualActiveSubsystemPartite A₀.ordered old.system
            e.toFunctionEmbedding).part x)
    (q : ℕ) (hq : q ≤ lowerCuts.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow lower κ) :
    let Target := actualActiveSubsystemPartite A₀.ordered old.system
      e.toFunctionEmbedding
    let E := lower.system.coarsenVia large lower.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure large.toRelStructure lower.system lowerFamily //
      b ∈ lower.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target large lower.system lower.isPartite lowerFamily
        hFamilyParts lower.selected i
    E.IsPartiteOver A₀.ordered ∧
      IrreduciblesExtendTo A₀.ordered E.toRelStructure ∧
      Function.Injective (fun i : I =>
        bSupportPiece A₀.ordered ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered
          (fun i : I => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (lowerCuts.length + 1)) (i : I)
        (a b : Embedding A₀.ordered Target.toRelStructure),
        lower.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        lowerTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      lower.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A₀.ordered) Target E κ := by
  classical
  have hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hRigid : ∀ b : Embedding A₀.ordered D, SameCopy b e → b = e := by
    intro b hb
    exact ordered_embedding_eq_of_sameCopy b e hb
  have hActive :
      (activeCarrier A₀.ordered old.system e.toFunctionEmbedding).Nonempty := by
    let u : UA := Classical.choice (inferInstance : Nonempty UA)
    exact ⟨projected.val u, ⟨projected, u, rfl⟩⟩
  exact ForestTailStage.trueActiveSelected_localInputBundle
    A₀.ordered old e large fineAllowed lower
    hA hBaseLinear hBaseStrong hRigid hActive projected hHigh
    hLarge hFamilyParts q hq κ hArrow

/-!
The nontrivial physical-fibre specialization is intentionally defined
only once, in TrainRecursiveOrderedNontrivialSelectedInputs.  That
independent clean-main module derives the same source-level inputs
directly from the actual two projected physical copies.  Do not
reintroduce a second declaration under the same global theorem name.
-/

/-- In the genuine nontrivial physical-fibre case, one actual pair of
distinct projected A-copy carriers simultaneously supplies the two
different A-copies in the *true* induced active lower target and all
seven coarsened selected local-input certificates. Neither a
separately selected projected copy nor an independent hTargetTwo
witness is assumed. The lower selected stage and its arrow remain
explicit conditional inputs; this is not the missing PictureStep. -/
theorem ForestTailStage.orderedTrueActiveSelected_pairAndBundle_of_nontrivial
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family t targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (large : StructuralRamsey.Partite.System L.withOrder UA Q)
    {lowerFamily : Set (Embedding
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure large.toRelStructure)}
    {lowerCuts : List ℕ}
    {lowerTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure) lowerCuts.length}
    (fineAllowed : Fin (lowerCuts.length + 1) → Set UA)
    (lower : ForestTailStage A₀.ordered
      (actualActiveSubsystemPartite A₀.ordered old.system
        e.toFunctionEmbedding).toRelStructure
      large.toRelStructure lowerFamily lowerCuts lowerTrain
      (fun ν => large.part ⁻¹' fineAllowed ν))
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A₀.ordered D (copyCarrier b.base))
    (hPhysical : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (hHigh : 3 ≤ t.headD 0)
    (hLarge : large.IsPartiteOver A₀.ordered)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A₀.ordered old.system e.toFunctionEmbedding,
        large.part (b x) =
          (actualActiveSubsystemPartite A₀.ordered old.system
            e.toFunctionEmbedding).part x)
    (q : ℕ) (hq : q ≤ lowerCuts.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow lower κ) :
    let Target := actualActiveSubsystemPartite A₀.ordered old.system
      e.toFunctionEmbedding
    let E := lower.system.coarsenVia large lower.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure large.toRelStructure lower.system lowerFamily //
      b ∈ lower.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target large lower.system lower.isPartite lowerFamily
        hFamilyParts lower.selected i
    (∃ a b : Embedding A₀.ordered Target.toRelStructure,
      ¬ SameCopy a b) ∧
    E.IsPartiteOver A₀.ordered ∧
      IrreduciblesExtendTo A₀.ordered E.toRelStructure ∧
      Function.Injective (fun i : I =>
        bSupportPiece A₀.ordered ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A₀.ordered
          (fun i : I => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (lowerCuts.length + 1)) (i : I)
        (a b : Embedding A₀.ordered Target.toRelStructure),
        lower.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        lowerTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      lower.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A₀.ordered) Target E κ := by
  classical
  obtain ⟨projected, partner, hDistinct⟩ := hPhysical
  constructor
  · exact activeTarget_twoGenuineCopies_of_nontrivialFibre
      A₀.ordered old.system e.toFunctionEmbedding
      ⟨projected, partner, hDistinct⟩
  · exact ForestTailStage.orderedTrueActiveSelected_localInputBundle
      A₀ old e large fineAllowed lower
      hBaseLinear hBaseStrong projected hHigh hLarge hFamilyParts q hq κ hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
