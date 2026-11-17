import Girth.Track5CoveredMarkedRamsey

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {V I W J : Type v} [LinearOrder W]

/-- The physical split edges of the marked witness are exactly the small
coloured-edge support of its actual induced ordered vertex type. -/
theorem ColouredEdgeOwnerSplit.selectedLiftCarrierFor_support_eq
    (H : ColouredEdgeOwnerSplit V I)
    (selected : J → ColouredOwnerSelectedCopy (W := W) H)
    (k : ℕ) (profile : Fin k → I)
    (E : Set (Set W)) (colour : W → I) (order : LinearOrder H.Vertex)
    (hSupport : supportCopies (colouredOrderedEdgeSource.{v, v} k profile)
      (colouredOrderedEdgeTarget k E colour) = E)
    (hSource : ∀ j, (selected j).sourceEdges = E)
    (hLift : ∀ j, ∃ s : Embedding
      (colouredOrderedEdgeTarget k E colour)
      ((@colouredOrderedEdgeTarget I H.Vertex k
        H.splitPhysicalEdges H.newPredicate order).induce
        (H.selectedLiftCarrierFor selected)),
      ∀ x, (s x).1 = (selected j).lift x)
    (hOwned : ∀ f : H.OldEdge, ∃ j, ∃ a : (selected j).SourceEdge,
      (selected j).physicalEdge a = f) :
    let S := H.selectedLiftCarrierFor selected
    let R := @colouredOrderedEdgeTarget I H.Vertex k
      H.splitPhysicalEdges H.newPredicate order
    supportCopies (colouredOrderedEdgeSource.{v,v} k profile) (R.induce S) =
      Set.range (fun f : H.SplitPhysicalEdge => Subtype.val ⁻¹' f.1) := by
  let A := colouredOrderedEdgeSource.{v,v} k profile
  let S := H.selectedLiftCarrierFor selected
  let R := @colouredOrderedEdgeTarget I H.Vertex k
    H.splitPhysicalEdges H.newPredicate order
  change supportCopies A (R.induce S) =
    Set.range (fun f : H.SplitPhysicalEdge => Subtype.val ⁻¹' f.1)
  apply Set.Subset.antisymm
  · rintro edge ⟨a, rfl⟩
    let b := (RelStructure.inclusion R S).comp a
    have hb : copyCarrier b ∈ H.splitPhysicalEdges :=
      @colouredOrderedEdgeEmbedding_carrier_mem I H.Vertex order
        k H.splitPhysicalEdges profile H.newPredicate b
    refine ⟨⟨copyCarrier b, hb⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, Subtype.ext hu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, rfl⟩
  · rintro edge ⟨f, rfl⟩
    obtain ⟨old, rfl⟩ := H.physicalSplitEdge_surjective f
    obtain ⟨j, e, he⟩ := hOwned old
    obtain ⟨s, hs⟩ := hLift j
    have hMem : e.1 ∈ supportCopies A (colouredOrderedEdgeTarget k E colour) := by
      rw [hSupport, ← hSource j]
      exact e.2
    obtain ⟨a, ha⟩ := hMem
    refine ⟨s.comp a, ?_⟩
    ext x
    change x.1 ∈ H.splitEdge old ↔ x ∈ copyCarrier (s.comp a)
    rw [← he, ← (selected j).lift_source_edge e, ha]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hu⟩
      exact ⟨u, Subtype.ext ((hs (a u)).trans hu)⟩
    · rintro ⟨u, rfl⟩
      exact ⟨a u, ⟨u, rfl⟩, (hs (a u)).symm⟩

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftCarrierFor_support_eq

end StructuralRamsey.Girth
