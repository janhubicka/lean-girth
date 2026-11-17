import Girth.Track5CoveredMarkedRamsey
import Girth.TrainFillingPrivateActualCompletedWFirstParameter
import Girth.TrainFillingPrivateCompletedWOrderedEHN

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v w
variable {I V : Type v} [LinearOrder I] [LinearOrder V] [Finite V]

/-- The actual first-wagon union of the original train has a covered
ordered Ramsey witness marked by the original bottom-to-first-wagon
parameter. The ambient edge family is the normalized complete support. -/
theorem actualFirstWagonCompletedW_markedRamsey
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (oldEdges : Set (Set V)) (colour : V → I)
    (hProfileOrder : ∀ i j : Fin k, profile i ≠ profile j →
      i < j → profile i < profile j)
    (hLinear : ALinear (colouredOrderedEdgeSource.{v,v} k profile)
      (colouredOrderedEdgeTarget k oldEdges colour))
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{v,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour)} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT (T.wagonClassCarrier (fun e => e.1) μ) g)
    (allowed : Set I)
    (hParameter : TrainParentIntersectionBound
      (T.wagonClassCarrier (fun e => e.1) (0 : Fin (m + 1)))
      (T.wagonParent (0 : Fin (m + 1)) μ
        (by change (0 : Nat) ≤ μ.val; omega))
      {x | colour x ∈ allowed})
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    let carrier := T.wagonClassCarrier (fun e => e.1) μ
    letI := T.wagonQuotientLinearOrder μ
    letI := firstWagonUnionOrder carrier colour
    let E := supportCopies (colouredOrderedEdgeSource.{v,v} k profile)
      (completedFirstWagonColouredUnion k oldEdges colour carrier)
    CoveredMarkedColouredWitness k E (firstWagonUnionColour carrier colour) allowed κ := by
  classical
  let A := colouredOrderedEdgeSource.{v,v} k profile
  let D := colouredOrderedEdgeTarget k oldEdges colour
  let carrier := T.wagonClassCarrier (fun e => e.1) μ
  letI := T.wagonQuotientLinearOrder μ
  letI := firstWagonUnionOrder carrier colour
  let W := completedFirstWagonColouredUnion k oldEdges colour carrier
  let E := supportCopies A W
  let colourW := firstWagonUnionColour carrier colour
  change CoveredMarkedColouredWitness k E colourW allowed κ
  have hSupport :
      supportCopies A (colouredOrderedEdgeTarget k E colourW) = E := by
    exact colouredOrderedEdgeSupport_normalized k
      (taggedFirstWagonEdges carrier oldEdges) profile colourW
  have hSource := (T.actualWagon_EHN_source_of_bound A D μ g hg hGirth).2
  have hCovered : ∀ x : FirstWagonUnionVertex carrier, ∃ e ∈ E, x ∈ e := by
    intro x
    obtain ⟨a, ha⟩ :=
      completedFirstWagon_covered k hk profile oldEdges colour carrier hSource x
    exact ⟨copyCarrier a, ⟨a, rfl⟩, ha⟩
  have hWLinear : ALinear A W :=
    completedFirstWagon_aLinear k hk profile oldEdges colour carrier
      (fun p => aLinear_induce hLinear (carrier p))
  have hMarked :=
    actualFirstWagonCompletedW_marked_of_parentBound
      k hk profile oldEdges colour T μ g hg hGirth allowed hParameter
  exact track5_exists_selectedColouredWitness_marked_covered k hk profile colourW E
    allowed hSupport hCovered hProfileOrder
    (fun x y h => completedFirstWagon_order_of_colour_lt carrier colour x y h)
    (girthGT_two_of_aLinear A W hWLinear)
    (fun e f he hf hne x hxe hxf => hMarked e f he hf hne ⟨hxe, hxf⟩)
    κ

#print axioms StructuralRamsey.Girth.actualFirstWagonCompletedW_markedRamsey

end StructuralRamsey.Girth
