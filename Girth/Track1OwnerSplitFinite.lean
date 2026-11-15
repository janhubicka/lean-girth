import Girth.TrainColouredEdgeOwnerSplit
import Mathlib.Data.Fintype.Powerset

/-!
# Numbered Track 1: finite selected-edge owner token universe

The owner-splitting vertex type consists of old vertices, the
finite collection of old physical edge names, and one bottom tag.
If the old EHN witness has finitely many vertices, all of these
types are finite automatically; there is no independent finiteness
assumption to establish for the projection-first order.

STAGED DRAFT, not compiled on this branch.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v}

/-- Every physical edge label is a subset of the finite old vertex
type, hence finite; the tagged union used by the owner split is finite. -/
theorem ColouredEdgeOwnerSplit.finite_ownerVertex
    (H : ColouredEdgeOwnerSplit V I) [Finite V] :
    Finite H.Vertex := by
  classical
  infer_instance

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.finite_ownerVertex

end StructuralRamsey.Girth
