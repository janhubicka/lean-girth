import Girth.TrainColouredOwnerExactColourTransfer
import Girth.TrainColouredOwnerSelectedLift
import Mathlib.Tactic

/-!
# Track 1: no unused owner-token vertices in the selected output

The physical owner-token ambient type contains formally possible tokens which
need not occur in any selected copy. Take the output vertex set to be the UNION
of the lifted selected copy ranges. The following statements certify exact
edge coverage, including the selected copies with isolated source vertices.

The nonempty old-edge selected-cover hypothesis is an explicit input:
it must be derived from the original selected-target union before extracting
the final coloured witness.

DRAFT / UNCOMPILED. No new kernel or axiom certificate.
-/

namespace StructuralRamsey.Girth

universe v
namespace ColouredEdgeOwnerSplit

variable {V I W : Type v} (H : ColouredEdgeOwnerSplit V I)
variable (selected : I → ColouredOwnerSelectedCopy (W := W) H)

/-- Exactly the vertices actually appearing in the selected lifted copies. -/
def selectedLiftCarrier : Set H.Vertex :=
  {z | ∃ i : I, z ∈ Set.range (selected i).lift}

/-- Exactly the edge images of the physical source edges in selected copies. -/
def selectedLiftEdges : Set (Set H.Vertex) :=
  {e | ∃ i : I, ∃ f : (selected i).SourceEdge,
    e = H.splitEdge ((selected i).physicalEdge f)}

/-- Every selected lifted source edge lies in the union of its selected
target carriers. No arbitrary owner-token is retained as a vertex. -/
theorem selectedLiftEdges_subset_carrier
    {e : Set H.Vertex} (he : e ∈ H.selectedLiftEdges selected) :
    e ⊆ H.selectedLiftCarrier selected := by
  obtain ⟨i, f, rfl⟩ := he
  intro z hz
  rw [← (selected i).lift_source_edge f] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨i, ⟨w, rfl⟩⟩

/-- Under the actual physical-edge coverage hypothesis, no split support
edge is lost when the final carrier is restricted to selected lifts. -/
theorem selectedLiftEdges_eq_splitPhysicalEdges
    (hOldCover : ∀ e : H.OldEdge,
      ∃ i : I, ∃ f : (selected i).SourceEdge,
        (selected i).physicalEdge f = e) :
    H.selectedLiftEdges selected = H.splitPhysicalEdges := by
  ext e
  constructor
  · rintro ⟨i, f, rfl⟩
    exact ⟨(selected i).physicalEdge f, rfl⟩
  · rintro ⟨old, rfl⟩
    obtain ⟨i, f, hf⟩ := hOldCover old
    refine ⟨i, f, ?_⟩
    rw [hf]

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftEdges_subset_carrier
#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftEdges_eq_splitPhysicalEdges

end ColouredEdgeOwnerSplit
end StructuralRamsey.Girth
