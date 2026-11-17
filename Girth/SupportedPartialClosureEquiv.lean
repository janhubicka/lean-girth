import Girth.SupportedPartialClosurePort

/-!
# Exact closure test for free gluing of supported partial operations

For a free support-graph union covering the ambient carrier, with a
symmetric support relation and a partial operation whose value is
adjacent to every input, the following are equivalent:

* the shared interface is closed under the operation;
* both original sides are closed in the union.

This is the positive closure component needed for coherent-interface
gluing. It is independent of tree-girth and of newly generated coloured
copies. The statement permits a relation for the graph of the partial
operation; function uniqueness may be imposed separately.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {n : ℕ}
variable {adj : W → W → Prop}
variable {step : (Fin n → W) → W → Prop}
variable {L R : Set W}

/-- In a free union of supported partial-operation structures, the
interface is closed precisely when both old sides remain closed. -/
theorem operationClosed_port_iff_sides
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSupport : OperationSupported (n := n) adj step) :
    OperationClosed step (L ∩ R) ↔
      OperationClosed step L ∧ OperationClosed step R := by
  constructor
  · intro hClosed
    exact ⟨old_left_operationClosed hCover hNoCross hSupport hClosed,
      old_right_operationClosed hCover hNoCross hSymm hSupport hClosed⟩
  · rintro ⟨hLeft, hRight⟩
    intro args z hArgs hStep
    exact ⟨hLeft args z (fun i => (hArgs i).1) hStep,
      hRight args z (fun i => (hArgs i).2) hStep⟩

end CoherentPort
end StructuralRamsey.Girth
