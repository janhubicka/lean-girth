import Girth.TrainPhysicalPartiteForestData
import Girth.TrainRecursiveProjectedBaseTwoForest
import Girth.TrainLabelledPhysicalToOrdinaryGirth

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA X : Type v}

/-- Turn the projected cutoff-two forest into the actual height-one train
witness using equality at the bottom and the universal relation at the top. -/
theorem finePartiteFtWitness_baseTwo_of_spanningTuple
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA X) [Finite X]
    (sourceTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered Target.toRelStructure) 1)
    (allowed : Fin 2 → Set UA)
    (active : Embedding A₀.ordered Target.toRelStructure)
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → UA),
      A₀.rel R z ∧ Function.Surjective z)
    (hFine : ∀ a : Embedding A₀.ordered Target.toRelStructure, ∀ u : UA,
      Target.part (a u) = u)
    (hLinear : ALinear A₀.ordered Target.toRelStructure)
    (hSupport : ∀ x : X, ∃ a : Embedding A₀.ordered Target.toRelStructure,
      x ∈ copyCarrier a)
    (hParameters : sourceTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' allowed ν))
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    Nonempty (FinePartiteFtWitness A₀.ordered Target [2] sourceTrain allowed κ) := by
  classical
  let A := A₀.ordered
  have hAllowed := (sourceTrain.adjacentParameters_heightOne_iff _ _).mp hParameters
  have hContacts (a b : Embedding A Target.toRelStructure) (hNe : ¬ SameCopy a b)
      (x : X) (hx : x ∈ copyCarrier a ∩ copyCarrier b) : Target.part x ∈ allowed 1 := by
    have hDistinct : actualEdge a ≠ actualEdge b := fun h => hNe (congrArg Subtype.val h)
    exact hAllowed (actualEdge a) (actualEdge b) hDistinct hx
  obtain ⟨Y, hY, I, hI, Core, f, hCoreFine, _hCoreLinear, hCoreCover, _hEdgeCover,
    hDistinctSupports, _hStrong, hForest, hCoreContacts, hArrow⟩ :=
    cutoffTwoProjectedPartiteForestRamsey A₀ Target hSpan hFine hLinear hSupport
      (allowed 1) hContacts κ
  let U := EdgeTrainLevels.heightOne (OldACarrierEdge A Core.toRelStructure)
  refine ⟨{
    Vertex := Y
    finiteVertex := hY
    Index := I
    finiteIndex := hI
    core := Core
    selected := f
    train := U
    fineEdges := hCoreFine
    supportNonempty := ?_
    supportCovers := ?_
    selectedSupports := hDistinctSupports
    mixedForest := hForest
    selectedTrain := ?_
    fineParameters := ?_
    positiveFull := ?_
    physicalArrow := ?_ }⟩
  · obtain ⟨i, _⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨actualEdge ((f i).toEmbedding.comp active)⟩
  · intro y
    obtain ⟨a, hy⟩ := hCoreCover y
    exact ⟨actualEdge a, hy⟩
  · intro μ i a b
    change U.rel μ (actualEdge ((f i).toEmbedding.comp a))
      (actualEdge ((f i).toEmbedding.comp b)) ↔ sourceTrain.rel μ (actualEdge a) (actualEdge b)
    fin_cases μ
    · rw [U.bottom, sourceTrain.bottom]
      constructor
      · intro h
        exact Subtype.ext (sameCopy_of_comp (f i).toEmbedding (congrArg Subtype.val h))
      · intro h
        apply Subtype.ext
        change copyCarrier ((f i).toEmbedding.comp a) =
          copyCarrier ((f i).toEmbedding.comp b)
        calc
          copyCarrier ((f i).toEmbedding.comp a) = (f i).toEmbedding '' copyCarrier a :=
            copyCarrier_comp_eq_image (f i).toEmbedding a
          _ = (f i).toEmbedding '' copyCarrier b :=
            congrArg (fun S : Set X => (f i).toEmbedding '' S) (congrArg Subtype.val h)
          _ = copyCarrier ((f i).toEmbedding.comp b) :=
            (copyCarrier_comp_eq_image (f i).toEmbedding b).symm
    · exact ⟨fun _ => sourceTrain.top _ _, fun _ => U.top _ _⟩
  · apply (U.adjacentParameters_heightOne_iff _ _).mpr
    intro p q hpq x hx
    obtain ⟨a, ha⟩ := p.2
    obtain ⟨b, hb⟩ := q.2
    have hNe : ¬ SameCopy a b := fun hEq =>
      hpq (Subtype.ext (ha.trans (hEq.trans hb.symm)))
    change x ∈ p.1 ∩ q.1 at hx
    rw [ha, hb] at hx
    exact hCoreContacts a b hNe x hx
  · intro j hj
    have hLt := j.isLt
    change j.val < 1 at hLt
    omega
  · intro χ
    exact hArrow (fun a => χ (actualEdge a))

/-- The projected forest proves the standalone assertion at cutoff `[2]`
when a relation tuple spans the ordered A-copy. -/
theorem finePartiteForestAssertion_baseTwo_of_spanningTuple
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (hSpan : ∃ (R : L.Symbol) (z : Fin (L.arity R) → UA),
      A₀.rel R z ∧ Function.Surjective z)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    FinePartiteForestAssertion A₀.ordered [2] κ := by
  intro X _ Target sourceTrain allowed hFine hSupport hTwo hParameters hGirth
  obtain ⟨active, _, _⟩ := hTwo
  have hOrdinary := ordinaryGirth_of_targetBottomLabelledCut A₀.ordered
    Target.toRelStructure sourceTrain 2 (hGirth 0)
  exact finePartiteFtWitness_baseTwo_of_spanningTuple A₀ Target sourceTrain allowed active
    hSpan hFine (aLinear_of_girthGT_two A₀.ordered Target.toRelStructure hOrdinary)
    hSupport hParameters κ

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
