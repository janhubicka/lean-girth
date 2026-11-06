import Girth.TrainRecursiveParameterRestrictionKernel
import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveWitnessPass
import Girth.ActualActivePartitePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual true-active SOURCE train inherits all old adjacent parameters

The old genuine ForestTailStage carries AdjacentParameters for its
COMPLETE ambient physical A-support edge train at every cut.

The q>2 lower recursive target has exactly the TRUE active vertex
carrier, with all its genuine induced physical A-edges. Passing from
the whole old ambient train to this source has two exact stages:

* injectively restrict physical edge labels to all ambient A-edges
  whose full carriers lie in the true active vertex set;
* identify these with all genuine A-edges of the exact induced
  source, using inducedACarrierToShared, and pull their physical
  carriers back along the true active subtype inclusion.

The generic wagonClassEmbedding_parent / adjacentParameters_restrict /
adjacentParameters_vertexPullback kernels establish that every
adjacent cut still satisfies the old sibling-intersection parameter.
The TRUE active A-part coordinate has no artificial extension to
all old ambient vertices: we use activeSourcePart_spec ONLY on
the actual active subtype.

The target train is the literal twice-restricted OLD train on actual
induced source A-edge labels; all original wagon equivalences and
their physical parent maps remain unchanged. This is the lower
source's old (UNREFINED) parameter certificate, not yet the full
first-wagon-refined target certificate. The inserted/retained parent
steps remain independent. No new girth or output SupremeCycleBound
is inferred, and no appendix input is used.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The actual induced true-active source train inherits the COMPLETE
old adjacent-parameter predicate, expressed in the exact A-parts
of its genuine active subsystem. There is no global part inverse
defined or assumed on unrelated ambient vertices. -/
theorem ForestTailStage.trueActive_originalTrainParameters
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    (((stage.train.restrict
      (sharedOldACarrierInclusion A stage.system.toRelStructure S)).restrict
      (inducedACarrierToShared A stage.system.toRelStructure S))).AdjacentParameters
        (fun edge : OldACarrierEdge A (stage.system.toRelStructure.induce S) =>
          edge.1)
        (fun ν => (activeSourcePart A stage.system e.toFunctionEmbedding) ⁻¹'
          (e.toFunctionEmbedding ⁻¹' allowed ν)) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let Source := stage.system.toRelStructure.induce S
  let keepOld := sharedOldACarrierInclusion
    A stage.system.toRelStructure S
  let keepSource := inducedACarrierToShared
    A stage.system.toRelStructure S
  let Tshared := stage.train.restrict keepOld
  let Tactive := Tshared.restrict keepSource
  have hShared : Tshared.AdjacentParameters
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (fun ν => stage.system.part ⁻¹' allowed ν) :=
    stage.train.adjacentParameters_restrict
      (fun edge : OldACarrierEdge A stage.system.toRelStructure => edge.1)
      keepOld
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      (fun _ => Set.Subset.rfl)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      stage.parameters
  have hActiveAmbient : Tactive.AdjacentParameters
      (fun edge : OldACarrierEdge A Source =>
        (Subtype.val : S → stage.Vertex) '' edge.1)
      (fun ν => stage.system.part ⁻¹' allowed ν) :=
    Tshared.adjacentParameters_restrict
      (fun edge : SharedOldACarrierEdge A stage.system.toRelStructure S =>
        edge.1.1)
      keepSource
      (fun edge : OldACarrierEdge A Source =>
        (Subtype.val : S → stage.Vertex) '' edge.1)
      (fun _ => Set.Subset.rfl)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      hShared
  have hOnSource : Tactive.AdjacentParameters
      (fun edge : OldACarrierEdge A Source => edge.1)
      (fun ν => (Subtype.val : S → stage.Vertex) ⁻¹'
        (stage.system.part ⁻¹' allowed ν)) :=
    Tactive.adjacentParameters_vertexPullback
      (fun edge : OldACarrierEdge A Source =>
        (Subtype.val : S → stage.Vertex) '' edge.1)
      (fun edge : OldACarrierEdge A Source => edge.1)
      (Subtype.val : S → stage.Vertex)
      (by
        intro edge x hx
        exact ⟨x, hx, rfl⟩)
      (fun ν => stage.system.part ⁻¹' allowed ν)
      hActiveAmbient
  have hAllowed : (fun ν : Fin (t.length + 1) =>
        (Subtype.val : S → stage.Vertex) ⁻¹'
          (stage.system.part ⁻¹' allowed ν)) =
      (fun ν : Fin (t.length + 1) =>
        (activeSourcePart A stage.system e.toFunctionEmbedding) ⁻¹'
          (e.toFunctionEmbedding ⁻¹' allowed ν)) := by
    funext ν
    ext x
    change stage.system.part x.val ∈ allowed ν ↔
      e.toFunctionEmbedding
        (activeSourcePart A stage.system e.toFunctionEmbedding x) ∈ allowed ν
    rw [activeSourcePart_spec A stage.system e.toFunctionEmbedding x]
  change Tactive.AdjacentParameters
    (fun edge : OldACarrierEdge A Source => edge.1)
    (fun ν => (activeSourcePart A stage.system e.toFunctionEmbedding) ⁻¹'
      (e.toFunctionEmbedding ⁻¹' allowed ν))
  rw [← hAllowed]
  exact hOnSource

end StructuralRamsey.Girth.TrainRecursiveWitness
