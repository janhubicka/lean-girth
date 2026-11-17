import Girth.TrainCoverageFreePhysicalCutoffTwoStep
import Girth.TrainCoverageFreePhysicalFineRamseyBase
import Girth.TrainCoverageFreePhysicalFineWitnessCoarsening
import Girth.TrainCoverageFreePhysicalFibrePass
import Girth.TrainCoverageFreePhysicalTrueActiveGirth
import Girth.TrainLabelledPhysicalToOrdinaryGirth
import Girth.TrainPhysicalPartiteProjectedForest
import Girth.TrainRecursiveWitnessProfiles

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- The raw cutoff-two filling on the actual fine-partite active train. -/
def ProjectedCutoffTwoLocalAssertion
    (A : RelStructure L UA) (tail : List ℕ) (κ : Type w) : Prop :=
  ∀ {X : Type v} [Finite X] (Target : StructuralRamsey.Partite.System L UA X)
    (original : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) (2 :: tail).length)
    (allowed : Fin ((2 :: tail).length + 1) → Set UA),
    Target.toRelStructure.IsHomomorphism A Target.part →
    (∀ (a : Embedding A Target.toRelStructure) x, Target.part (a x) = x) →
    (∀ x, ∃ a : Embedding A Target.toRelStructure, x ∈ copyCarrier a) →
    (∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b) →
    ALinear A Target.toRelStructure →
    original.AdjacentParameters (fun edge => edge.1) (fun ν => Target.part ⁻¹' allowed ν) →
    (∀ j : Fin tail.length, LabelledGirthGT
      (original.wagonClassCarrier (fun edge => edge.1) j.castSucc.succ) (tail.get j)) →
    ∃ (Y I : Type v) (_ : Finite Y) (_ : Finite I),
      Nonempty (CutoffTwoRawLocalData (Y := Y) (I := I) A Target tail original allowed κ)

variable {VB P : Type v}

/-- The cutoff-two finite pass uses raw filling on nontrivial fibres. -/
theorem ramseyForest_cutoffTwo
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nontrivial UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P} [Finite P]
    {family : Set (Embedding B D)} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (2 :: tail).length}
    {allowed : Fin ((2 :: tail).length + 1) → Set P}
    (S : PhysicalForestStage A₀.ordered B D family (2 :: tail) targetTrain allowed)
    (ht : Admissible (2 :: tail)) (κ : Type w) [Nonempty κ]
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong : ∀ b ∈ family, AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (hInitial : S.CoversBase)
    (hProject : S.system.toRelStructure.IsHomomorphism D S.system.part)
    (hBaseArrow : ∀ χ : Embedding A₀.ordered D → κ, ∃ b ∈ family,
      ∀ a₁ a₂ : Embedding A₀.ordered B, χ (b.comp a₁) = χ (b.comp a₂))
    (hLocal : ProjectedCutoffTwoLocalAssertion A₀.ordered tail κ) :
    ∃ R : PhysicalForestStage A₀.ordered B D family (2 :: tail) targetTrain allowed,
      R.system.toRelStructure.IsHomomorphism D R.system.part ∧ DesignatedArrow R κ := by
  let A := A₀.ordered
  let Ready (_ : List (UA ↪ P))
      (T : PhysicalForestStage A B D family (2 :: tail) targetTrain allowed) :=
    T.CoversBase ∧ T.system.toRelStructure.IsHomomorphism D T.system.part
  obtain ⟨T, hT, hArrow⟩ := PhysicalForestStage.ramseyPass S
    (projectionProfileList UA P) κ Ready ⟨hInitial, hProject⟩ mem_projectionProfileList
    hBaseArrow hInitial (by
      intro α remaining T hCurrent
      exact PhysicalForestStage.profileStep_of_nontrivialStep A₀ T α remaining κ Ready
        hCurrent (fun _ => hCurrent) (fun e hPair hReady => by
          let E := actualActiveSubsystemPartite A T.system e.toFunctionEmbedding
          have hFine (a : Embedding A E.toRelStructure) (x : UA) : E.part (a x) = x :=
            actualActiveSubsystemPartite_fineEdges_of_projectedACopies A D T.system
              T.projectsACopies e (fun b hb => ordered_embedding_eq_of_sameCopy b e hb) a x
          have hCovered (x : _) : ∃ a : Embedding A E.toRelStructure, x ∈ copyCarrier a := by
            obtain ⟨edge, ⟨a, rfl⟩, hx⟩ :=
              actualRecursiveActiveSupport_cover A T.system e.toFunctionEmbedding x
            exact ⟨a, hx⟩
          have hCuts (j : Fin tail.length) :=
            PhysicalForestStage.trueActive_cutGirth_of_fullSystem T e j.succ.castSucc
              (tail.get j) (T.tailGirth j.succ (Nat.succ_pos j.val))
          obtain ⟨Y, I, hY, hI, ⟨W⟩⟩ := hLocal E (T.activeFineTrain e)
            (fun ν => e.toFunctionEmbedding ⁻¹' allowed ν)
            (activeFine_isHomomorphism_of_partProjection A D T.system e hReady.2)
            hFine hCovered
            (activeTarget_twoGenuineCopies_of_nontrivialFibre A T.system e.toFunctionEmbedding hPair)
            (aLinear_induce T.aLinear (activeCarrier A T.system e.toFunctionEmbedding))
            (PhysicalForestStage.trueActive_fineParameters T e) hCuts
          let : Finite Y := hY
          let : Finite I := hI
          obtain ⟨a, _, _⟩ := hPair
          obtain ⟨N, hN, hStep⟩ := CutoffTwoRawLocalData.toProjectedForestStep A₀ T e
            a κ W ht hReady.2 hBaseLinear hReady.1 hBaseStrong hTargetTwo
          exact ⟨N, ⟨hStep.coversBase hReady.1, hN⟩, hStep⟩))
  exact ⟨T, hT.2, hArrow⟩

/-- Start from the actual linear Ramsey base and extract the complete
cutoff-two forest witness from the final selected picture. -/
theorem projectedFinePartiteForest_cutoffTwo
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA), A₀.rel r z ∧ Function.Surjective z)
    (tail : List ℕ) (ht : Admissible (2 :: tail))
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hLocal : ProjectedCutoffTwoLocalAssertion A₀.ordered tail κ) :
    ProjectedFinePartiteForestAssertion A₀.ordered (2 :: tail) κ := by
  intro X _ Target targetTrain fineAllowed hTargetProject hFine hSupport hTwo hParameters hCuts
  let A := A₀.ordered
  have hGirth := ordinaryGirth_of_targetBottomLabelledCut A Target.toRelStructure targetTrain 2
    (hCuts ⟨0, by simp⟩)
  obtain ⟨P, hFinite, D, family, hBaseFine, hBaseLinear, _hBaseCovers,
      hFamilyParts, hFamilyStrong, hBaseArrow, hBaseProject⟩ :=
    exists_projectingFinePartiteRamseyBase_of_spanningTuple A₀ Target hTargetProject
      hFine hSupport hTwo hGirth hSpan κ
  letI : Finite P := hFinite
  let allowed : Fin ((2 :: tail).length + 1) → Set P := fun ν => D.part ⁻¹' fineAllowed ν
  have hOldAllowed (b : family) (ν : Fin ((2 :: tail).length + 1)) :
      b.val ⁻¹' allowed ν = Target.part ⁻¹' fineAllowed ν := by
    ext x
    change D.part (b.val x) ∈ fineAllowed ν ↔ Target.part x ∈ fineAllowed ν
    rw [hFamilyParts b.val b.property x]
  have hBaseParameters (b : family) : targetTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => b.val ⁻¹' allowed ν) := by
    simpa only [hOldAllowed b] using hParameters
  have hSupportNonempty : Nonempty (OldACarrierEdge A Target.toRelStructure) := by
    obtain ⟨a, _, _⟩ := hTwo
    exact ⟨actualEdge a⟩
  have hSupportCovers (x : X) : ∃ e : OldACarrierEdge A Target.toRelStructure, x ∈ e.1 := by
    obtain ⟨a, hx⟩ := hSupport x
    exact ⟨actualEdge a, hx⟩
  let : Nonempty family := by
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A Target.toRelStructure D.toRelStructure
      family κ hBaseArrow
    exact ⟨⟨b, hb⟩⟩
  let hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  let data := initialTail_of_targetCuts A hA Target.toRelStructure D.toRelStructure family
    (2 :: tail) ht targetTrain hSupportNonempty hGirth (fun j _ => hCuts j)
  let old := initialForestTailStage_of_tail A hA Target.toRelStructure D.toRelStructure family
    (2 :: tail) ht targetTrain allowed hSupportNonempty hSupportCovers hGirth hBaseParameters data
  let S := PhysicalForestStage.ofStrong hA (ForestStage.ofStrong old)
  have hInitial : S.CoversBase := by
    intro b hb
    exact ⟨initialDesignatedCopy Target.toRelStructure D.toRelStructure family ⟨b, hb⟩,
      Set.mem_range_self _, rfl⟩
  obtain ⟨R, hProject, hArrow⟩ := ramseyForest_cutoffTwo A₀ S ht κ hBaseLinear hFamilyStrong
    hTwo hInitial old.isPartite.1 hBaseArrow hLocal
  let W := PhysicalForestStage.toFinePartiteFtWitness Target D R fineAllowed
    (fun _ => rfl) hProject hBaseFine (fun b _ x => hFamilyParts b.base b.base_mem x) hArrow
  refine ⟨W, ?_⟩
  change R.system.toRelStructure.IsHomomorphism A (D.part ∘ R.system.part)
  intro r z hz
  exact hBaseProject r (R.system.part ∘ z) (hProject r z hz)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
