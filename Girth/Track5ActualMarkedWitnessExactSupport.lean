import Girth.Track5ActualCompletedWMarkedRamsey
import Girth.Track5MarkedWitnessExactSupport

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v w
variable {I V : Type v} [LinearOrder I] [LinearOrder V] [Finite V]

/-- The actual first-wagon witness has the same selected embeddings and
colouring arrow on its complete induced ordered carrier. Every physical
split edge gives exactly one member of that carrier's small-edge support. -/
theorem actualFirstWagonCompletedW_markedRamsey_exactSupport
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
    let colourW := firstWagonUnionColour carrier colour
    ∃ (Y J : Type v) (H : ColouredEdgeOwnerSplit Y I)
      (selected : J → ColouredOwnerSelectedCopy
        (W := FirstWagonUnionVertex carrier) H)
      (order : LinearOrder H.Vertex),
      let S := H.selectedLiftCarrierFor selected
      let R := (@colouredOrderedEdgeTarget I H.Vertex k
        H.splitPhysicalEdges H.newPredicate order).induce S
      let edgeCarrier := fun f : H.SplitPhysicalEdge =>
        (Subtype.val : S → H.Vertex) ⁻¹' f.1
      Finite S ∧ Finite J ∧ H.allowed = allowed ∧
      (∀ j, (selected j).sourceEdges = E) ∧
      (∀ j, ∃ s : Embedding (colouredOrderedEdgeTarget k E colourW) R,
        ∀ x, (s x).1 = (selected j).lift x) ∧
      (∀ f : H.OldEdge, ∃ j, ∃ e : (selected j).SourceEdge,
        (selected j).physicalEdge e = f) ∧
      (∀ e ∈ H.splitPhysicalEdges, e ⊆ S) ∧
      (∀ z : S, ∃ e : H.SplitPhysicalEdge, z.1 ∈ e.1) ∧
      (∀ e f : H.SplitPhysicalEdge, e ≠ f →
        e.1 ∩ f.1 ⊆ {z | H.newPredicate z ∈ allowed}) ∧
      GirthGT H.splitPhysicalEdges 2 ∧
      (∀ j, ∀ f : H.OldEdge, ∀ x y : H.Vertex,
        x ≠ y → x ∈ H.splitEdge f → y ∈ H.splitEdge f →
        x ∈ Set.range (selected j).lift → y ∈ Set.range (selected j).lift →
        ∃ e : (selected j).SourceEdge, (selected j).physicalEdge e = f) ∧
      (∀ χ : H.SplitPhysicalEdge → κ, ∃ j,
        ∀ e f : (selected j).SourceEdge,
          χ (H.physicalSplitEdge ((selected j).physicalEdge e)) =
          χ (H.physicalSplitEdge ((selected j).physicalEdge f))) ∧
      Function.Injective edgeCarrier ∧
      supportCopies (colouredOrderedEdgeSource.{v,v} k profile) R =
        Set.range edgeCarrier := by
  let carrier := T.wagonClassCarrier (fun e => e.1) μ
  letI := T.wagonQuotientLinearOrder μ
  letI := firstWagonUnionOrder carrier colour
  let A := colouredOrderedEdgeSource.{v,v} k profile
  let E := supportCopies A
    (completedFirstWagonColouredUnion k oldEdges colour carrier)
  let colourW := firstWagonUnionColour carrier colour
  have hWitness : CoveredMarkedColouredWitness k E colourW allowed κ :=
    actualFirstWagonCompletedW_markedRamsey k hk profile oldEdges colour
      hProfileOrder hLinear T μ g hg hGirth allowed hParameter κ
  obtain ⟨Y, J, H, selected, order, hFinite, hFiniteJ, hAllowed,
    hSource, _, hOwned, hLift, hCover, hPoints, hMarked,
    hSystemGirth, _, hStrong, _, hArrow⟩ := hWitness
  have hSourceExact : supportCopies A
      (colouredOrderedEdgeTarget k E colourW) = E :=
    colouredOrderedEdgeSupport_normalized k
      (taggedFirstWagonEdges carrier oldEdges) profile colourW
  let val : H.selectedLiftCarrierFor selected → H.Vertex := Subtype.val
  have hFull (f : H.SplitPhysicalEdge) : val '' (val ⁻¹' f.1) = f.1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hCover f.1 f.2 hx⟩, hx, rfl⟩
  have hInjective : Function.Injective
      (fun f : H.SplitPhysicalEdge => val ⁻¹' f.1) := by
    intro e f hef
    apply Subtype.ext
    exact (hFull e).symm.trans ((congrArg (Set.image val) hef).trans (hFull f))
  letI : Finite H.Vertex := hFinite
  refine ⟨Y, J, H, selected, order, inferInstance, hFiniteJ, hAllowed,
    hSource, hLift, hOwned, hCover, hPoints, hMarked, hSystemGirth,
    hStrong, hArrow, hInjective, ?_⟩
  exact H.selectedLiftCarrierFor_support_eq selected
    k profile E colourW order hSourceExact hSource hLift hOwned

#print axioms StructuralRamsey.Girth.actualFirstWagonCompletedW_markedRamsey_exactSupport

end StructuralRamsey.Girth
