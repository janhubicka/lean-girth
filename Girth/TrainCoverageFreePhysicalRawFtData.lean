import Girth.TrainCoverageFreePhysicalActiveWagonData
import Girth.TrainActiveGluingWitness
import Girth.TrainPhysicalPartiteForestData

set_option autoImplicit false
set_option Elab.async false

/-!
# RAW physical F_t witness with fine edge parts, not ordered IsPartiteOver

This record contains exactly the type of local F_t data used by the
physical selected attachment: the true active source, a finite witness
of the same one-edge coloured type, one selected embedding per
physical support image, the same-q mixed finite SET forests, exact
train restrictions, positive full-system bounds, parameters, and
indexed PHYSICAL A-edge colouring arrow.

Crucially, its fineEdges field states only that every physical
A-embedding uses the prescribed fine A-part labels. It does NOT
postulate IsPartiteOver of the full order-expanded ambient structure,
mixedCoverage, output girth or an already-constructed PictureStep.
A separate theorem constructs the PictureStep using the source-level
weak physical stage attachment. The abstract F_t existence assertion
is not formally constructed here. UNCOMPILED SOURCE.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The standalone witness specialised to the true active subsystem and
its inherited train. -/
abbrev RawPartiteFtWitness
    (A₀ : RelStructure L UA) [LinearOrder UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (stage : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed)
    (e : Embedding A₀.ordered D) (κ : Type w) :=
  FinePartiteFtWitness A₀.ordered
    (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding)
    (q :: tail)
    (PhysicalForestStage.activeFineTrain stage e)
    (fun ν => e.toFunctionEmbedding ⁻¹' allowed ν) κ

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
