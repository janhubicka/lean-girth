import Girth.TrainFillingPrivateTailWagonEquiv
import Girth.TrainFillingIndexedPrivateParentParameters

set_option Elab.async false

/-!
# Transfer actual ORIGINAL train parameters through private filling

The shortened first-wagon train is the ACTUAL tail quotient
of the original height-(m+1) train T. At each new level nu
the shortened wagon carrier equals the complete original
old-(nu+1) wagon carrier, and the parent maps commute.

The old parameter restriction at nu+1 -> mu+1 therefore
transfers to the shortened quotient before filling.
The checked PrivateWagonInput.expandedWagonClass_parentBound
then transfers it to the full private X-coordinate carriers.

This is a direct application of two existing preparation
lemmas, not a new private-overlap argument and not a
postulated parameter bound on the output witness.

Source candidate; actual local kernel build pending.
-/

namespace StructuralRamsey.Girth

universe v
variable {E V X : Type v}

/-- Original allowed-part parent/child bounds are inherited
by the TRUE private shortened first-wagon construction.

The equation hCarrier says that the private input uses
the original first-wagon carriers literally; it is
definitionally true for the actual EHN-summand input.
It is NOT a girth/output-bound hypothesis. -/
theorem PrivateWagonInput.expandedActualTail_parentBound
    {m : ℕ}
    (Told : EdgeTrainLevels E (m + 1))
    (oldEdges : E → Set V)
    (U : PrivateWagonInput V Told.FirstWagon X)
    (hCarrier : U.oldCarrier =
      Told.wagonClassCarrier oldEdges
        (EdgeTrainLevels.firstWagonLevel m))
    (ν μ : Fin (m + 1)) (hνμ : ν ≤ μ)
    (allowed : Set V)
    (hOld : TrainParentIntersectionBound
      (Told.wagonClassCarrier oldEdges ν.succ)
      (Told.wagonParent ν.succ μ.succ
        (by
          change ν.val + 1 ≤ μ.val + 1
          omega)) allowed) :
    TrainParentIntersectionBound
      ((Told.tailQuotient).wagonClassCarrier
        (fun p => Set.range (U.place p)) ν)
      ((Told.tailQuotient).wagonParent ν μ hνμ)
      ((Sum.inl : V → U.Vertex) '' allowed) := by
  have hTransferred :
      TrainParentIntersectionBound
        ((Told.tailQuotient).wagonClassCarrier
          (Told.wagonClassCarrier oldEdges
            (EdgeTrainLevels.firstWagonLevel m)) ν)
        ((Told.tailQuotient).wagonParent ν μ hνμ)
        allowed :=
    Told.tailQuotient_parentIntersectionBound
      oldEdges ν μ hνμ allowed hOld
  have hOldLocal :
      TrainParentIntersectionBound
        ((Told.tailQuotient).wagonClassCarrier U.oldCarrier ν)
        ((Told.tailQuotient).wagonParent ν μ hνμ)
        allowed := by
    rw [hCarrier]
    exact hTransferred
  exact U.expandedWagonClass_parentBound Told.tailQuotient
    ν μ hνμ allowed hOldLocal

end StructuralRamsey.Girth
