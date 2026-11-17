import Girth.TrainRecursiveActiveIrreducibleCoverage
import Girth.Track1CutoffThreeLocalRamsey
import Girth.TrainRecursiveTrueActiveCoverage
import Girth.TrainRecursivePartiteBaseInitial
import Girth.TrainRecursiveTrueActiveAdjacentParameters
import Girth.TrainRecursiveTrueActiveHJSource
import Girth.TrainRecursiveUniformPartiteForest

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- A nonempty true active fibre at height one admits an actual local picture
step with triangle-free support and the original allowed contacts. -/
theorem ForestTailStage.coveredBaseThree_pictureStep
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) 1}
    {allowed : Fin 2 → Set P}
    (stage : ForestTailStage A₀.ordered B D family [3] targetTrain allowed)
    (hBaseLinear : ALinear A₀.ordered D)
    (hBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A₀.ordered D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (e : Embedding A₀.ordered D)
    (hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered
      stage.system e.toFunctionEmbedding, ¬ SameCopy a.val b.val)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ next : ForestTailStage A₀.ordered B D family [3] targetTrain allowed,
      PictureStep stage next e.toFunctionEmbedding κ := by
  classical
  obtain ⟨active, other, hPair⟩ := hPair
  let A := A₀.ordered
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let Target := actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding
  have hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hStrong (b : DesignatedCopy B D stage.system family) (_ : b ∈ stage.selected) :
      AStrong A D (copyCarrier b.base) := hBaseStrong b.base b.base_mem
  have hRigid (a : Embedding A D) (hEq : SameCopy a e) : a = e :=
    ordered_embedding_eq_of_sameCopy a e hEq
  have hActive : S.Nonempty := by
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨active.val u, projected_mem_activeCarrier A stage.system
      e.toFunctionEmbedding active u⟩
  have hCoverage : IrreduciblesExtendTo A Target.toRelStructure :=
    activeSubsystem_irreduciblesExtendTo_of_selectedMixedCoverage
      stage.system stage.selected stage.isPartite stage.mixedCoverage hA hBaseLinear
      hStrong e hRigid hActive
  have hEdge : Nonempty (Embedding A Target.toRelStructure) :=
    ⟨(activeProjectedPartite A stage.system e.toFunctionEmbedding active).toEmbedding⟩
  obtain ⟨hTarget, _, hSupport⟩ := stage.trueActive_HJ_sourceGeometry A B D e
  have hStageGirth : GirthGT (supportCopies A stage.system.toRelStructure) 3 := by
    apply girthGT_of_finiteMixedForestThrough _ _ 3 stage.bottomForest
    rintro edge ⟨a, rfl⟩
    exact Or.inl ⟨a, rfl⟩
  have hTargetGirth : GirthGT (supportCopies A Target.toRelStructure) 3 :=
    supportGirthGT_induce A stage.system.toRelStructure S 3 hStageGirth
  obtain ⟨p, q, hpq⟩ := activeSupport_two_distinct_of_projected_carriers
    A stage.system e.toFunctionEmbedding active other hPair
  have hTwo : ∃ p q : Set S, p ∈ supportCopies A Target.toRelStructure ∧
      q ∈ supportCopies A Target.toRelStructure ∧ p ≠ q :=
    ⟨p.1, q.1, p.2, q.2, fun h => hpq (Subtype.ext h)⟩
  have hParameters := stage.trueActive_inducedAdjacentParameters e
  let permitted : Set UA := e.toFunctionEmbedding ⁻¹' allowed 1
  have hContacts (a b : Embedding A Target.toRelStructure) (hNe : ¬ SameCopy a b)
      (x : S) (hx : x ∈ copyCarrier a ∩ copyCarrier b) :
      Target.part x ∈ permitted := by
    have hDistinct : actualEdge a ≠ actualEdge b := fun hSame =>
      hNe (congrArg Subtype.val hSame)
    exact (EdgeTrainLevels.adjacentParameters_heightOne_iff _ _ _).mp hParameters
      (actualEdge a) (actualEdge b) hDistinct hx
  obtain ⟨o, hMono⟩ := exists_cutoffTwo_partiteAuxiliaryOrder A₀ Target hTarget
  letI : LinearOrder S := o
  obtain ⟨Y, hY, I, hI, E, f, hPartiteE, hCoverageE, hGirthE, hInjE,
      hForestE, hContactsE, hArrow⟩ :=
    cutoffThreeCoveredPartiteLocalRamsey A₀ Target hTarget hTargetGirth hCoverage
      hSupport hEdge hMono permitted hContacts κ
  letI : Finite Y := hY
  letI : Finite I := hI
  let Core := E.relabel e.toFunctionEmbedding
  let F := fun i => activePartiteToRelabelledCore A stage.system
    e.toFunctionEmbedding E (f i)
  let U := EdgeTrainLevels.heightOne (OldACarrierEdge A Core.toRelStructure)
  have hCoreParameters :
      U.AdjacentParameters (fun edge => edge.1) (fun ν => Core.part ⁻¹' allowed ν) := by
    apply (U.adjacentParameters_heightOne_iff _ _).mpr
    intro p q hpq x hx
    obtain ⟨a, ha⟩ := p.2
    obtain ⟨b, hb⟩ := q.2
    have hNe : ¬ SameCopy a b := fun hEq =>
      hpq (Subtype.ext (ha.trans (hEq.trans hb.symm)))
    change x ∈ p.1 ∩ q.1 at hx
    rw [ha, hb] at hx
    exact hContactsE a b hNe x hx
  let bounds : ActiveAttachmentBounds stage hA e active Core F U := {
    corePartite := StructuralRamsey.Partite.Induced.relabel_isPartiteOver A E hPartiteE e
    coreCoverage := hCoverageE
    baseStrong := hStrong
    targetTwo := hTargetTwo
    interior := by intro μ hPos hLt; change μ.val < 1 at hLt; omega
    bottomTwo := by decide
    localForest := Or.inr ⟨hTwo, hInjE, hForestE⟩
    coreGirth := fun _ => hGirthE
    cutoffTwo := by intro h; change 3 = 2 at h; omega
    coreParameters := hCoreParameters
    interiorFull := by intro μ hPos hLt; change μ.val < 1 at hLt; omega
    tailSupreme := by intro j hj; have hLt : j.val < 1 := j.isLt; omega
  }
  exact ⟨stage.activeAttachment_of_local_bounds hA hBaseLinear e hRigid active
    Core F U bounds,
    stage.activeAttachment_pictureStep_of_familyArrow hA hBaseLinear e hRigid active
      Core F U bounds κ hArrow⟩

/-- The fixed-base height-one forest witness follows by the ordinary finite
pass. No first-wagon refinability and no positive-cut bound are needed. -/
theorem uniformSelectedPartiteForest_baseThree
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    UniformSelectedPartiteForest A₀ [3] κ := by
  intro VB P hFiniteVB hFiniteP Target Large family ht hTarget _hLinearTarget
    hTwo _hLarge hLinearLarge hStrong hParts targetTrain allowed
    hSupportNonempty hSupportCovers hGirth hParameters _hCuts hPartiteArrow
  letI : Finite VB := hFiniteVB
  letI : Finite P := hFiniteP
  have hRelationalArrow :=
    relationalDesignatedArrow_of_partiteFamily_for_orderedA
      A₀ Target Large family hTarget κ hPartiteArrow
  haveI : Nonempty family := by
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A₀.ordered
      Target.toRelStructure Large.toRelStructure family κ hRelationalArrow
    exact ⟨⟨b, hb⟩⟩
  obtain ⟨stage, _, hArrow⟩ := constructFromInitial_of_nontrivialSteps
    A₀ Target.toRelStructure Large.toRelStructure family [3] ht
    targetTrain (fun ν => Large.part ⁻¹' allowed ν)
    hSupportNonempty hSupportCovers hGirth
    (targetParameters_of_partiteFamily_preimage A₀.ordered Target Large
      family hParts targetTrain allowed hParameters)
    (by intro j hj; have hLt : j.val < 1 := j.isLt; omega)
    κ hRelationalArrow (fun _ _ => True) trivial (fun _ _ _ _ _ => trivial)
    (by
      intro e _remaining old hPair _
      obtain ⟨next, hStep⟩ := old.coveredBaseThree_pictureStep
        A₀ hLinearLarge hStrong hTwo e hPair κ
      exact ⟨next, trivial, hStep⟩)
  exact ⟨stage, hArrow⟩

#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.ForestTailStage.coveredBaseThree_pictureStep
#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.uniformSelectedPartiteForest_baseThree

end StructuralRamsey.Girth.TrainRecursiveWitness
