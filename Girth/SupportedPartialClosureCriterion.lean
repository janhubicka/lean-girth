import Girth.SupportedPartialClosureEquiv

/-!
# Exact local closure test for arbitrary supported partial operations

The midpoint special case is proved in FreePortClosureCriterion.
Here we generalize to an arbitrary finite-arity operation relation:

If the output of an operation is support-adjacent to every input,
the support graph is freely amalgamated over an operation-closed
interface, and the union covers the ambient carrier, then a subset
X is operation-closed exactly if:
  (1) X restricted to either old side is operation-closed INSIDE
      that side; and
  (2) every operation with arguments from X appearing on BOTH
      opposite private sides has its output in X.

When an operation involves inputs private to opposite sides, its
output is forced into the port by mixed_operation_output_mem_port.
This is thus a completely local closure certificate for every
candidate coloured A-occurrence.

No Ramsey arrow or higher support-copy girth conclusion is claimed.
A 0-ary operation is allowed: in that case the mixed condition is
vacuous, but a closed port already forces every nullary value into
both old sides.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {n : ℕ}
variable {adj : W → W → Prop}
variable {step : (Fin n → W) → W → Prop}
variable {L R : Set W}

/-- Closure of S relative to operation values that lie in a given
ambient side. -/
def OperationClosedInside
    (step : (Fin n → W) → W → Prop)
    (ambient S : Set W) : Prop :=
  ∀ (args : Fin n → W) (z : W),
    (∀ i : Fin n, args i ∈ S) →
    z ∈ ambient → step args z → z ∈ S

/-- The exact arbitrary-arity closed-port criterion.
Unlike the P4-specialized birth lemma, no new coloured-copy
shape assumption is imposed. -/
theorem operationClosed_iff_sidewise_and_crossPort
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSupport : OperationSupported (n := n) adj step)
    (hPort : OperationClosed step (L ∩ R))
    (X : Set W) :
    OperationClosed step X ↔
      OperationClosedInside step L (X ∩ L) ∧
      OperationClosedInside step R (X ∩ R) ∧
      (∀ (args : Fin n → W) (z : W),
        (∀ i : Fin n, args i ∈ X) →
        step args z →
        (∃ i : Fin n, args i ∈ L \ R) →
        (∃ j : Fin n, args j ∈ R \ L) → z ∈ X) := by
  classical
  constructor
  · intro hClosed
    refine ⟨?_, ?_, ?_⟩
    · intro args z hArgs hzL hz
      exact ⟨hClosed args z (fun i => (hArgs i).1) hz, hzL⟩
    · intro args z hArgs hzR hz
      exact ⟨hClosed args z (fun i => (hArgs i).1) hz, hzR⟩
    · intro args z hArgs hz _ _
      exact hClosed args z hArgs hz
  · rintro ⟨hLeft, hRight, hCross⟩
    intro args z hArgs hz
    by_cases hAllL : ∀ i : Fin n, args i ∈ L
    · have hzL : z ∈ L :=
        old_left_operationClosed hCover hNoCross hSupport hPort
          args z hAllL hz
      exact (hLeft args z (fun i => ⟨hArgs i, hAllL i⟩) hzL hz).1
    · by_cases hAllR : ∀ i : Fin n, args i ∈ R
      · have hzR : z ∈ R :=
          old_right_operationClosed hCover hNoCross hSymm hSupport hPort
            args z hAllR hz
        exact (hRight args z (fun i => ⟨hArgs i, hAllR i⟩) hzR hz).1
      · have hSomeLeftPrivate : ∃ i : Fin n, args i ∈ L \ R := by
          obtain ⟨i, hiNotR⟩ := not_forall.mp hAllR
          have hArgCover : args i ∈ L ∪ R := by
            rw [hCover]
            exact Set.mem_univ _
          exact ⟨i, ⟨hArgCover.resolve_right hiNotR, hiNotR⟩⟩
        have hSomeRightPrivate : ∃ j : Fin n, args j ∈ R \ L := by
          obtain ⟨j, hjNotL⟩ := not_forall.mp hAllL
          have hArgCover : args j ∈ L ∪ R := by
            rw [hCover]
            exact Set.mem_univ _
          exact ⟨j, ⟨hArgCover.resolve_left hjNotL, hjNotL⟩⟩
        exact hCross args z hArgs hz
          hSomeLeftPrivate hSomeRightPrivate

/-- For mixed input tuples, outputs are not merely in X: the
support geometry forces them to lie in the common port.
This is the exact "port address" form of the closure certificate. -/
theorem operationClosed_mixed_output_mem_X_and_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSupport : OperationSupported (n := n) adj step)
    (X : Set W)
    (hClosed : OperationClosed step X)
    (args : Fin n → W) (z : W)
    (hArgs : ∀ i, args i ∈ X) (hz : step args z)
    (i j : Fin n)
    (hi : args i ∈ L \ R)
    (hj : args j ∈ R \ L) :
    z ∈ X ∩ (L ∩ R) := by
  exact ⟨hClosed args z hArgs hz,
    mixed_operation_output_mem_port
      hCover hNoCross hSymm hSupport args z hz i j hi hj⟩

end CoherentPort
end StructuralRamsey.Girth
