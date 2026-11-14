import Girth.TrainRecursiveActualLowerTailSupreme
import Girth.TrainRecursiveFineWitnessStep
import Girth.TrainRecursiveTrueActiveIndexedNontrivialInputs
import Girth.TrainRecursiveActualHeightCutoffApplication
import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

/-!
# A genuine lower selected stage gives the nontrivial refining picture step

This theorem fills the local step interface for the q>2 case, conditional
only on an ACTUAL selected lower ForestTailStage with its DesignatedArrow.
The lower target is exactly the old true active subsystem with its given
FirstWagonRefinement, not an A-sized-base relabeling or a selected-edge
subsystem. The lower stage is over a sufficiently large A-partite base.

The proof constructs the fine family, its literal selected-index Ramsey
arrow and all physical input geometry. The original positive tail
SupremeCycleBound is derived from the actual lower stage, not assumed.
All q-1/q fine system bounds and canonical permitted parts are derived.

This is NOT a final recursive existence theorem: the lower stage and its
DesignatedArrow must be obtained at a strictly smaller cutoff rank. In
particular one may not supply a PictureStep at the current rank to construct
that same lower witness. No output invariant is postulated here.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P V : Type v}

/-- Given a *genuine* selected lower witness for the entire refined active
target, construct the next actual stage and preserve refinement readiness
for the unprocessed profiles. The lower selected copy index is retained
literally, with no carrier quotient and no ambient-edge deletion. -/
theorem ForestTailStage.refiningPictureStep_of_actualLowerSelectedStage
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A₀.ordered B D family (q :: tail)
      targetTrain allowed)
    (ht : Admissible (q :: tail)) (hq : 2 < q)
    (e : Embedding A₀.ordered D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered old.system e.toFunctionEmbedding,
      copyCarrier a.val ≠ copyCarrier b.val)
    (R : FirstWagonRefinement
      (old.train.restrict (sharedOldACarrierInclusion
        A₀.ordered old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge => edge.1.1) old.system.part
      (allowed ⟨1, by simp⟩) (q - 1))
    (Large : StructuralRamsey.Partite.System L.withOrder UA V)
    [Finite V]
    {lowerFamily : Set (Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    (lower : ForestTailStage A₀.ordered
      (old.system.toRelStructure.induce
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      ((R.train.restrict (inducedACarrierToShared
        A₀.ordered old.system.toRelStructure
        (activeCarrier A₀.ordered old.system e.toFunctionEmbedding))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
      (fun ρ => Large.part ⁻¹'
        (fineAllowedFromRefinement
          (q :: tail).length R.extraCuts
          (by simp : 0 < (q :: tail).length)
          e.toFunctionEmbedding allowed R.permitted
          (Fin.cast (congrArg (fun k : ℕ => k + 1)
            (actualReplicatedCutoff_height_eq q R.extraCuts tail)).symm ρ))))
    (hBaseLinear : ALinear A₀.ordered D)
    (hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (hLarge : Large.IsPartiteOver A₀.ordered)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A₀.ordered old.system e.toFunctionEmbedding,
        Large.part (b x) =
          (actualActiveSubsystemPartite A₀.ordered old.system
            e.toFunctionEmbedding).part x)
    (κ : Type w) [Nonempty κ]
    (hLowerArrow : DesignatedArrow lower κ)
    (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady
      (by simp : 0 < (q :: tail).length) (q - 1)
      (e.toFunctionEmbedding :: remaining) old) :
    ∃ next : ForestTailStage A₀.ordered B D family
        (q :: tail) targetTrain allowed,
      ForestTailStage.FirstRefinementReady
        (by simp : 0 < (q :: tail).length) (q - 1)
        remaining next ∧
      PictureStep old next e.toFunctionEmbedding κ := by
  classical
  let A := A₀.ordered
  let m := (q :: tail).length
  let d := R.extraCuts
  let lowerCuts := List.replicate (d + 1) (q - 1) ++ tail
  let hLen : lowerCuts.length = m + d :=
    actualReplicatedCutoff_height_eq q d tail
  let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure Large.toRelStructure
    lower.system lowerFamily // b ∈ lower.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite
      lowerFamily hFamilyParts lower.selected i
  let T := lower.train.castHeight hLen
  let fineAllowed := fineAllowedFromRefinement m d
    (by simp : 0 < m) e.toFunctionEmbedding allowed R.permitted
  let fineAllowedLower : Fin (lowerCuts.length + 1) → Set UA :=
    fun ρ => fineAllowed (Fin.cast
      (congrArg (fun k : ℕ => k + 1) hLen) ρ)
  have hBaseStrong : ∀ b : DesignatedCopy B D old.system family,
      b ∈ old.selected → AStrong A D (copyCarrier b.base) := by
    intro b _
    exact hStrong b.base b.base_mem
  have hLowerBudget : q - 1 ≤ lowerCuts.headD 0 := by
    simp [lowerCuts, List.replicate_succ]
  have hIndexed :=
    old.orderedTrueActiveSelected_indexedInputAndTwoCopies_of_nontrivial
      A₀ e Large fineAllowedLower lower hBaseLinear hBaseStrong hPair
      (by omega : 3 ≤ q) hLarge hFamilyParts
      (q - 1) hLowerBudget κ hLowerArrow
  rcases hIndexed with
    ⟨_hTwo, hPartite, hEcoverage, hInjective, hForest,
      _hRestrictionLower, hParametersLower, hIndexedArrow⟩
  have hRigid : ∀ a : Embedding A D, SameCopy a e → a = e :=
    fun a ha => ordered_embedding_eq_of_sameCopy a e ha
  have hTwoCut : ∀ j : Fin (q :: tail).length, 0 < j.val →
      2 ≤ (q :: tail).get j := by
    intro j _
    exact ht.two_le _ (List.get_mem _)
  have hTail := old.attachedAllPositiveSupreme_of_refinedSelectedLower
    A (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    B D e active R Large lower hFamilyParts
    hTwoCut hStrong hTargetTwo hBaseLinear hRigid
  have hRestriction : ∀ (ν : Fin (m + d + 1)) (i : I)
      (a b : Embedding A (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))),
      T.rel ν (actualEdge ((f i).toEmbedding.comp a))
        (actualEdge ((f i).toEmbedding.comp b)) ↔
      (R.train.restrict (inducedACarrierToShared A
        old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding))).rel ν
          (actualEdge a) (actualEdge b) := by
    exact lower.coarsenedSelected_trainRestriction_castBack
      A Target Large
      (R.train.restrict (inducedACarrierToShared
        A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding)))
      hLen hFamilyParts
  have hAllowedIndex (ν : Fin (m + d + 1)) :
      fineAllowedLower (Fin.cast
        (congrArg (fun k : ℕ => k + 1) hLen).symm ν) =
        fineAllowed ν := by
    cases hLen
    rfl
  have hParameters : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν) := by
    have hCast := lower.train.castHeight_adjacentParameters
      (fun edge => edge.1) hLen
      (fun ρ => E.part ⁻¹' fineAllowedLower ρ)
      hParametersLower
    simpa only [hAllowedIndex] using hCast
  have hAllowed := fineAllowedFromRefinement_all_constraints
    m d (by simp : 0 < m) e.toFunctionEmbedding allowed R.permitted
    R.permitted_subset R.permitted_subsingleton
  rcases hAllowed with ⟨hSingleton, hFirst, hRetained⟩
  have hFull : ∀ ν : Fin (m + d + 1), 0 < ν.val →
      ν.val < m + d →
      (activeGluingWitnessOrderOneData A old.system
        e.toFunctionEmbedding E.toRelStructure
        (fun i => (f i).toEmbedding) T ν).FullSystemGirthGT
          (if ν.val ≤ d then q - 1 else q) := by
    intro ν hPos hInterior
    exact lower.coarsenedSelected_fullSystem_for_actualHeight
      A old.system e.toFunctionEmbedding Large hFamilyParts
      ht.nondecreasing ν hPos hInterior
  exact old.refiningPictureStep_of_fineWitness
    A₀ hBaseLinear e active E f
    (by simp : 0 < m) hq R T fineAllowed
    hPartite hEcoverage hBaseStrong hTargetTwo hPair
    hInjective hForest hRestriction hParameters
    hSingleton hFirst hRetained hFull hTail
    remaining hFresh hReady κ hIndexedArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
