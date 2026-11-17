import Girth.TrainCoverageFreePhysicalStage
import Girth.TrainRecursiveFineWitnessTransport
import Girth.ActualActivePartitePresentation
import Girth.LabelledWagonCutRestriction

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB} {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The inherited train on all physical A-edges of the true active subsystem. -/
abbrev PhysicalForestStage.activeFineTrain
    (stage : PhysicalForestStage A B D family t targetTrain allowed)
    (e : Embedding A D) :
    EdgeTrainLevels (OldACarrierEdge A
      (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure)
      t.length :=
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  (stage.train.restrict (sharedOldACarrierInclusion A stage.system.toRelStructure S)).restrict
    (inducedACarrierToShared A stage.system.toRelStructure S)

namespace Physical

/-- Labelled wagon girth of the actual active source at the inherited vector. -/
def PhysicalForestStage.ActiveWagonGirth
    (A₀ : RelStructure L UA) [LinearOrder UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) : Prop :=
  ∀ j : Fin (q :: tail).length,
    LabelledGirthGT ((stage.activeFineTrain e).wagonClassCarrier
      (fun edge => edge.1) j.castSucc) ((q :: tail).get j)

end Physical

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
