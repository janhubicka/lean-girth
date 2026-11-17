import Girth.TrainFillingPrivateActualCompletedWMarked
import Girth.TrainSharedEdgeQuotients
import Girth.TrainParameterRestriction

set_option Elab.async false

/-!
# Source first-train parameter yields the exact physical edge overlap bound

TrainParentIntersectionBound at the equality-to-first-wagon
parent map is the genuine first train parameter A₁.
At equality cut zero every wagon contains just its one
physical edge, and distinct edges have distinct zero-wagon
labels. Projecting both labels to a common first-wagon
ancestor is exactly the first-wagon relation T.rel μ.

Therefore a genuine TrainParentIntersectionBound of
the ORIGINAL train implies that distinct original
A-support edges in the SAME first wagon intersect
only in permitted old vertices. This is the one
source-side premise needed by the completed-W
marked owner-splitting lemma.

No output property, chosen Ramsey witness, or external
arbitrary edge-owner map is assumed.

Uncompiled Lean source candidate.
-/

namespace StructuralRamsey.Girth

universe v
variable {E V : Type v}

/-- At the original equality cut the complete wagon
carrier of a physical edge is EXACTLY the edge itself. -/
theorem EdgeTrainLevels.zeroWagonClassCarrier_eq_edge
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set V) (e : E) :
    T.wagonClassCarrier edge 0
      (Quotient.mk (T.wagonSetoid 0) e) = edge e := by
  ext x
  constructor
  · rintro ⟨f, hef, hx⟩
    have hEq : e = f := (T.bottom e f).mp hef
    subst f
    exact hx
  · intro hx
    exact ⟨e, (T.equivalent 0).refl e, hx⟩

/-- Distinct genuine physical edges have distinct original
equality-cut wagon labels; no physical multiplicity is
collapsed before the first parent projection. -/
theorem EdgeTrainLevels.zeroWagonLabels_ne
    {m : ℕ} (T : EdgeTrainLevels E m)
    (e f : E) (hne : e ≠ f) :
    (Quotient.mk (T.wagonSetoid 0) e) ≠
      Quotient.mk (T.wagonSetoid 0) f := by
  intro h
  exact hne ((T.bottom e f).mp (Quotient.exact h))

/-- The ORIGINAL source train's allowed-part intersection
bound between its bottom equality edge labels and their
first-wagon ancestors implies the exact old-physical-edge
form used by the marked completed-W construction.

At cutoff two specialize μ to the genuine first-wagon
level 1 and allowed to vertices whose predicate lies in A₁. -/
theorem EdgeTrainLevels.firstParameter_physicalEdge_inter_allowed
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set V)
    (μ : Fin (m + 1)) (allowed : Set V)
    (hParameter : TrainParentIntersectionBound
      (T.wagonClassCarrier edge (0 : Fin (m + 1)))
      (T.wagonParent (0 : Fin (m + 1)) μ
        (by change (0 : Nat) ≤ μ.val; omega))
      allowed)
    (e f : E) (hne : e ≠ f)
    (hSameWagon : T.rel μ e f) :
    edge e ∩ edge f ⊆ allowed := by
  let bottom : Fin (m + 1) := 0
  let he : Quotient (T.wagonSetoid bottom) :=
    Quotient.mk (T.wagonSetoid bottom) e
  let hf : Quotient (T.wagonSetoid bottom) :=
    Quotient.mk (T.wagonSetoid bottom) f
  have hDifferent : he ≠ hf :=
    T.zeroWagonLabels_ne e f hne
  have hSameParent :
      T.wagonParent bottom μ
        (by change (0 : Nat) ≤ μ.val; omega) he =
      T.wagonParent bottom μ
        (by change (0 : Nat) ≤ μ.val; omega) hf := by
    change Quotient.mk (T.wagonSetoid μ) e =
      Quotient.mk (T.wagonSetoid μ) f
    exact Quotient.sound hSameWagon
  have hSmall := hParameter hDifferent hSameParent
  have heCarrier :
      T.wagonClassCarrier edge bottom he = edge e :=
    T.zeroWagonClassCarrier_eq_edge edge e
  have hfCarrier :
      T.wagonClassCarrier edge bottom hf = edge f :=
    T.zeroWagonClassCarrier_eq_edge edge f
  simpa only [heCarrier, hfCarrier] using hSmall

end StructuralRamsey.Girth
