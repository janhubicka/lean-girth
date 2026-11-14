import Girth.TrainColouredOwnerProjectionOrder
import Girth.TrainColouredOwnerExactColourTransfer
import Girth.Track1OwnerSplitCoverage

/-!
# Track 1: one global order and the physical edge Ramsey arrow

This packages two established owner-splitting interfaces for the exact
selected family. It does not yet construct full ordered induced embeddings
or the original EHN selected-arrow input. This is a conditional helper.

DRAFT, NOT KERNEL-CHECKED at the current head.
-/

namespace StructuralRamsey.Girth

universe v w

namespace ColouredEdgeOwnerSplit

variable {V I W Choice : Type v} {κ : Type w}

/-- The actual physical edge splitting admits one global projection-first
order compatible with ALL selected target lifts, and transports the
selected old edge-colouring Ramsey property. -/
theorem track1_selectedOrder_and_edgeRamsey
    (H : ColouredEdgeOwnerSplit V I)
    [LinearOrder V] [LinearOrder W] [Finite H.Vertex]
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hMono : ∀ c : Choice, StrictMono (selected c).embedding)
    (hArrow : ∀ χ : H.OldEdge → κ,
      ∃ c : Choice, ∀ a b : (selected c).SourceEdge,
        χ ((selected c).physicalEdge a) =
          χ ((selected c).physicalEdge b)) :
    ∃ o : LinearOrder H.Vertex,
      (∀ c : Choice, ∀ x y : W, x < y →
        @LT.lt H.Vertex o.toLT ((selected c).lift x) ((selected c).lift y)) ∧
      (∀ χ : H.SplitPhysicalEdge → κ,
        ∃ c : Choice, ∀ a b : (selected c).SourceEdge,
          χ (H.physicalSplitEdge ((selected c).physicalEdge a)) =
            χ (H.physicalSplitEdge ((selected c).physicalEdge b))) := by
  obtain ⟨o, hProj⟩ := H.exists_projectionFirstLinearOrder
  refine ⟨o, ?_, ?_⟩
  · intro c x y hxy
    exact H.selectedLift_strictMono_of_projectionFirst
      (selected c) o hProj (hMono c) x y hxy
  · intro χ
    exact H.selectedColourTransfer selected hArrow χ

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.track1_selectedOrder_and_edgeRamsey

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
