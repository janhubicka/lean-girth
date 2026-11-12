import Girth.TrainRecursiveSelectedFineTrainHeight
import Girth.TrainRecursiveActualAttachedPositive
import Girth.TrainRecursiveCoarsenedSelectedIndexedBundle
import Girth.TrainRecursiveNontrivialActiveCoverage
import Girth.TrainRecursiveFineWitnessStep
import Girth.TrainRecursiveCanonicalFineParametersCast
import Girth.TrainRecursiveActualHeightCutoffApplication
import Girth.TrainRecursiveSelectedLowerActualInputs
import Girth.TrainRecursiveWitness
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Nontrivial q>2 selected picture step from one ACTUAL lower Ramsey witness

This is the local finite picture-step assembly for the genuine ordered
source. The recursive lower ForestTailStage is at the literal cutoff list
replicate (R.extraCuts+1) (q-1) ++ tail, on the exact true active induced
source with R's actual first-wagon train and canonical allowed A-parts.

The already-validated interfaces provide ALL the local fine-witness data:
* true active irreducible A-coverage from nontrivial projected copies;
* A-partite selected core, physical support injectivity, mixed bottom forest
  and a genuinely indexed selected partite Ramsey arrow;
* complete fine train reflection and adjacent parameters at the true height;
* all three canonical first-refinement allowed-set constraints;
* global full-system girth at every positive fine cut at q-1/q thresholds;
* all original positive attached SupremeCycleBound certificates.

The existing refiningPictureStep_of_fineWitness then constructs the next
selected stage and its actual PictureStep, preserving refinability of all
fresh unprocessed profiles. The genuine lower selected stage and its
DesignatedArrow are still premises, to be obtained by well-founded
induction. This does not prove cutoff-two or global recursive existence.
No physical edge or literal selected label is discarded.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P V : Type v}

/-- The TRUE nontrivial ordered q>2 local step, conditional only on the
genuine selected lower-stage recursive witness and the standing old
base/refinement geometry, not on separate fine-witness fields. -/
theorem ForestTailStage.actualNontrivialPictureStep_of_selectedLower
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family (q :: tail)
      targetTrain allowed)
    (e : Embedding A₀.ordered D)
    (ht : Admissible (q :: tail))
    (hq : 2 < q)
    (hBaseLinear : ALinear A₀.ordered D)
    (hStrong : ∀ r : Embedding B D, r ∈ family →
      AStrong A₀.ordered D (copyCarrier r))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (R : FirstWagonRefinement
      (old.train.restrict (sharedOldACarrierInclusion A₀.ordered
        old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge : SharedOldACarrierEdge A₀.ordered
        old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding) =>
          edge.1.1)
      old.system.part (allowed ⟨1, by simp⟩) (q - 1))
    (Large : StructuralRamsey.Partite.System L.withOrder UA V)
    (hLarge : Large.IsPartiteOver A₀.ordered)
    {lowerFamily : Set (Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A₀.ordered old.system e.toFunctionEmbedding,
        Large.part (b x) =
          activeSourcePart A₀.ordered old.system e.toFunctionEmbedding x)
    (lower : ForestTailStage A₀.ordered
      (old.system.toRelStructure.induce
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      ((R.train.restrict (inducedACarrierToShared A₀.ordered
        old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
      (fun ρ => Large.part ⁻¹'
        (fineAllowedFromRefinement
          (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length)
          e.toFunctionEmbedding allowed R.permitted
          (Fin.cast (congrArg (fun k : ℕ => k + 1)
            (actualReplicatedCutoff_height_eq q R.extraCuts tail)) ρ))))
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow lower κ)
    (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady
      (by simp : 0 < (q :: tail).length) (q - 1)
      (e.toFunctionEmbedding :: remaining) old) :
    ∃ next : ForestTailStage A₀.ordered B D family (q :: tail)
        targetTrain allowed,
      ForestTailStage.FirstRefinementReady
        (by simp : 0 < (q :: tail).length) (q - 1) remaining next ∧
      PictureStep old next e.toFunctionEmbedding κ := by
  classical
  let A := A₀.ordered
  let m := (q :: tail).length
  have hm : 0 < m := by simp [m]
  let lowerCuts := List.replicate (R.extraCuts + 1) (q - 1) ++ tail
  have hLen : lowerCuts.length = m + R.extraCuts :=
    actualReplicatedCutoff_height_eq q R.extraCuts tail
  let Target := actualActiveSubsystemPartite A old.system
    e.toFunctionEmbedding
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure lower.system lowerFamily // b ∈ lower.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite lowerFamily
      hFamilyParts lower.selected i
  let T := lower.train.castHeight hLen
  let fineAllowed : Fin (m + R.extraCuts + 1) → Set UA :=
    fineAllowedFromRefinement m R.extraCuts hm
      e.toFunctionEmbedding allowed R.permitted
  let lowerAllowed : Fin (lowerCuts.length + 1) → Set UA :=
    fun ρ => fineAllowed
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ρ)
  have hA : A.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected →
      AStrong A D (copyCarrier b.base) := by
    intro b _
    exact hStrong b.base b.base_mem
  have hHigh : 3 ≤ (q :: tail).headD 0 := by
    change 3 ≤ q
    omega
  have hTargetCoverage : IrreduciblesExtendTo A Target.toRelStructure :=
    old.orderedTrueActive_irreduciblesExtendTo_of_nontrivial
      A₀ hBaseLinear hBaseStrong e hPair hHigh
  have hLowerHead : q - 1 ≤ lowerCuts.headD 0 := by
    simp [lowerCuts, List.replicate_succ]
  have hInputs := lower.coarsenedSelected_actualIndexedLocalInputBundle
    A Target Large lowerFamily lowerAllowed hLarge hTargetCoverage
    hFamilyParts (q - 1) hLowerHead κ hArrow
  rcases hInputs with
    ⟨hPartite, hCoverage, hInjective, hForest,
      _hLowerRestriction, _hLowerParameters, hIndexedArrow⟩
  obtain ⟨active, _, _⟩ := hPair
  have hRestriction := lower.coarsenedSelected_fineRestriction_castHeight
    A Target Large
    (R.train.restrict (inducedACarrierToShared A
      old.system.toRelStructure
      (activeCarrier A old.system e.toFunctionEmbedding)))
    hLen hFamilyParts
  have hParameters : T.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν) :=
    lower.coarsened_adjacentParameters_castHeight_preimage
      A Target.toRelStructure Large lowerAllowed hLen.symm
  obtain ⟨hSingleton, hFirst, hRetained⟩ :=
    R.canonicalFineAllowed_all_constraints
      allowed e.toFunctionEmbedding
  have hFull : ∀ ν : Fin (m + R.extraCuts + 1),
      0 < ν.val → ν.val < m + R.extraCuts →
      (activeGluingWitnessOrderOneData A old.system
        e.toFunctionEmbedding E.toRelStructure
        (fun i : I => (f i).toEmbedding) T ν).FullSystemGirthGT
        (if ν.val ≤ R.extraCuts then q - 1 else q) := by
    intro ν hPos hInterior
    exact lower.coarsenedSelected_fullSystem_for_actualHeight
      A old.system e.toFunctionEmbedding Large hFamilyParts
      ht.nondecreasing ν hPos hInterior
  have hTwoCut : ∀ j : Fin (q :: tail).length,
      0 < j.val → 2 ≤ (q :: tail).get j := by
    intro j _
    exact ht.two_le _ (List.get_mem (q :: tail) j)
  have hRigid : ∀ a : Embedding A D, SameCopy a e → a = e :=
    fun a ha => ordered_embedding_eq_of_sameCopy a e ha
  have hTail : ∀ j : Fin (q :: tail).length,
      0 < j.val →
      (attachedSelectedPictureOrderOneData A hA B D
        old.system family old.selected e E.toRelStructure
        (fun i : I => (f i).toEmbedding)
        old.train (T.forgetFirstCuts hm)
        (activeCarrier_all_standard_copies_meet_core A old.system
          e.toFunctionEmbedding active I)
        j.castSucc).SupremeCycleBound ((q :: tail).get j) := by
    exact ForestTailStage.attachedAllPositiveSupreme_of_realRefinedLower
      A hA B D old e active Large R lower hFamilyParts
      hTwoCut hStrong hTargetTwo hBaseLinear hRigid
  exact ForestTailStage.refiningPictureStep_of_fineWitness
    A₀ old hBaseLinear e active E f hm hq R T fineAllowed
    hPartite hCoverage hBaseStrong hTargetTwo hPair
    hInjective hForest hRestriction hParameters
    hSingleton hFirst hRetained hFull hTail
    remaining hFresh hReady κ hIndexedArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
