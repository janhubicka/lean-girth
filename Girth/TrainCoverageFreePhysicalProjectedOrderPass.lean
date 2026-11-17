import Girth.TrainCoverageFreePhysicalFibrePass
import Girth.TrainRecursiveWitnessProfiles

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- At each step the old bottom system bound, coverage of selected bases,
and the relation projection into the base are retained together. -/
theorem PhysicalForestStage.ramseyOrder_of_projectingSteps
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P} [Finite P]
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (S : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (κ : Type w) [Nonempty κ] (hInitial : S.Ready)
    (hProject : S.system.toRelStructure.IsHomomorphism D S.system.part)
    (hBaseArrow : ∀ χ : Embedding A₀.ordered D → κ, ∃ b ∈ family,
      ∀ a₁ a₂ : Embedding A₀.ordered B, χ (b.comp a₁) = χ (b.comp a₂))
    (localStep : ∀ (e : Embedding A₀.ordered D)
      (T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed),
      T.Ready → T.system.toRelStructure.IsHomomorphism D T.system.part →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered T.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      ∃ O : PhysicalOrderStage A₀.ordered B D family (q :: tail) targetTrain allowed,
        O.system.toRelStructure.IsHomomorphism D O.system.part ∧
        PictureStep T O.toPhysicalForestStage e.toFunctionEmbedding κ) :
    ∃ R : PhysicalOrderStage A₀.ordered B D family (q :: tail) targetTrain allowed,
      R.system.toRelStructure.IsHomomorphism D R.system.part ∧
      DesignatedArrow R.toPhysicalForestStage κ := by
  let Ready (_ : List (UA ↪ P))
      (T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed) :=
    T.Ready ∧ T.system.toRelStructure.IsHomomorphism D T.system.part
  obtain ⟨T, hT, hArrow⟩ := PhysicalForestStage.ramseyPass S
    (projectionProfileList UA P) κ Ready ⟨hInitial, hProject⟩ mem_projectionProfileList
    hBaseArrow hInitial.2 (by
      intro α remaining T hCurrent
      exact PhysicalForestStage.profileStep_of_nontrivialStep A₀ T α remaining κ Ready
        hCurrent (fun _ => hCurrent) (fun e hPair hReady => by
          obtain ⟨O, hO, hStep⟩ := localStep e T hReady.1 hReady.2 hPair
          have hBottom : O.toPhysicalForestStage.BottomReady := by
            simpa [PhysicalForestStage.BottomReady] using O.allCutGirth
              (⟨0, by simp⟩ : Fin (q :: tail).length)
          exact ⟨O.toPhysicalForestStage, ⟨⟨hBottom, hStep.coversBase hReady.1.2⟩, hO⟩,
            hStep⟩))
  exact ⟨T.withBottom hT.1.1, hT.2, hArrow⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
