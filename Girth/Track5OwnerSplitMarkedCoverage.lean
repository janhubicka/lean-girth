import Girth.Track1SelectedCarrierEmbedding
import Girth.TrainColouredOwnerExactColourTransfer

namespace StructuralRamsey.Girth.ColouredEdgeOwnerSplit

universe v
variable {V I W Choice : Type v}

/-- The used carrier of an owner-split selected family is covered by actual
split edges whenever the selected source is covered by its own edges. The
split introduces no intersection outside the prescribed predicates. -/
theorem selectedLiftCarrierFor_marked_covered
    (H : ColouredEdgeOwnerSplit V I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hCovered : ∀ c w, ∃ e : (selected c).SourceEdge, w ∈ e.1) :
    (∀ z : H.selectedLiftCarrierFor selected,
      ∃ e : H.SplitPhysicalEdge, z.1 ∈ e.1) ∧
    (∀ e f : H.SplitPhysicalEdge, e ≠ f →
      e.1 ∩ f.1 ⊆ {z | H.newPredicate z ∈ H.allowed}) := by
  constructor
  · rintro ⟨z, c, w, rfl⟩
    obtain ⟨e, hw⟩ := hCovered c w
    refine ⟨H.physicalSplitEdge ((selected c).physicalEdge e), ?_⟩
    rw [H.physicalSplitEdge_carrier, ← (selected c).lift_source_edge e]
    exact ⟨w, hw, rfl⟩
  · intro e f hne z hz
    obtain ⟨a, rfl⟩ := H.physicalSplitEdge_surjective e
    obtain ⟨b, rfl⟩ := H.physicalSplitEdge_surjective f
    have hab : a ≠ b := fun h => hne (congrArg H.physicalSplitEdge h)
    obtain ⟨x, hx, rfl⟩ := H.intersection_only_allowed a b hab z hz.1 hz.2
    exact hx

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftCarrierFor_marked_covered

end StructuralRamsey.Girth.ColouredEdgeOwnerSplit
