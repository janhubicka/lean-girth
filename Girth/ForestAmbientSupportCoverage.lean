import Girth.ForestAllSupportGirth
import Girth.Berge

/-!
# Full ambient girth from a supported-copy forest and edge ownership

The verified forest girth theorem controls exactly the union of intrinsic
support edges belonging to named B/A pieces. It does NOT by itself
control other A-copies appearing in the ambient decorated structure.

The remaining geometric/relational input is therefore stated as the
precise coverage hypothesis that every actual ambient A-support edge
belongs to at least one selected forest piece's intrinsic support.
Under this hypothesis, ambient girth follows immediately.

This is a clean interface for the circulation proof's irreducible
A-copy ownership and for any proposed independent successor-tree proof.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- An ambient support-edge family is fully accounted for by the
intrinsic support edges of a selected family of hypergraph pieces. -/
def SupportCoveredByFamily
    (H : Set (Set W)) (F : I → HypergraphPiece W) : Prop :=
  H ⊆ ⋃ i : I, (F i).edges

/-- A supported-copy forest whose member supports have girth >g
forces ambient girth >g, PROVIDED every ambient A-edge is owned
by the selected family. No unsupported ambient edge is discarded. -/
theorem girthGT_of_forest_support_coverage
    [Fintype I]
    (H : Set (Set W))
    (F : I → HypergraphPiece W)
    (hForest : ForestOfCopies F)
    (g : ℕ)
    (hPieces : ∀ i : I, GirthGT (F i).edges g)
    (hCovered : SupportCoveredByFamily H F) :
    GirthGT H g := by
  exact girthGT_of_subset hCovered
    (girthGT_union_of_forest F hForest g hPieces)

/-- The intrinsic A-edge union of an already-verified forest
always meets the coverage condition exactly. -/
theorem union_supportCoveredByFamily
    (F : I → HypergraphPiece W) :
    SupportCoveredByFamily (⋃ i : I, (F i).edges) F := by
  intro e he
  exact he

end StructuralRamsey.Girth
