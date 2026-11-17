import Girth.FreePortMidpointClosed

/-!
# Supported partial-function closures across free amalgamation ports

This is the closure-neutral gluing lemma suggested by the midpoint
specialization. For a finite-arity partial operation represented by its
graph (an arbitrary relation step args output), suppose EVERY input is
adjacent in the support graph to the output. Then gluing over a port
closed under this operation preserves closure of both old sides.

The operation may be multi-valued here; functionality or uniqueness
can be added independently. In applications such as the midpoint
operation of girth-five graphs, functionality comes from the
absence of 4-cycles.

This is a geometric and closure statement ONLY: it does not ensure
preservation of high girth, the Ramsey arrow, or the absence of newly
born coloured configurations that cross the interface.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {n : ℕ}
variable {adj : W → W → Prop}
variable {step : (Fin n → W) → W → Prop}
variable {L R : Set W}

/-- Every argument of an operation instance is support-adjacent to
the resulting value. In the graph-midpoint case both arguments are
joined by an edge to their common neighbour. -/
def OperationSupported
    (adj : W → W → Prop)
    (step : (Fin n → W) → W → Prop) : Prop :=
  ∀ (args : Fin n → W) (z : W),
    step args z → ∀ i : Fin n, adj (args i) z

/-- Closedness under the (possibly partial, possibly multivalued)
operation relation. -/
def OperationClosed
    (step : (Fin n → W) → W → Prop)
    (S : Set W) : Prop :=
  ∀ (args : Fin n → W) (z : W),
    (∀ i : Fin n, args i ∈ S) → step args z → z ∈ S

/-- A free union over an operation-closed interface does not create
a new operation value outside the left side on old left arguments. -/
theorem old_left_operationClosed
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSupport : OperationSupported (n := n) adj step)
    (hPort : OperationClosed step (L ∩ R)) :
    OperationClosed step L := by
  intro args z hArgs hz
  by_contra hnotL
  have hzR : z ∈ R := by
    have h : z ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ z
    rcases h with hl | hr
    · exact False.elim (hnotL hl)
    · exact hr
  have hAllPort : ∀ i : Fin n, args i ∈ L ∩ R := by
    intro i
    have hL : args i ∈ L := hArgs i
    have hR : args i ∈ R := by
      by_contra hNotR
      exact hNoCross ⟨hL, hNotR⟩ ⟨hzR, hnotL⟩ (hSupport args z hz i)
    exact ⟨hL, hR⟩
  exact hnotL (hPort args z hAllPort hz).1

/-- Symmetric closure-preservation theorem. -/
theorem old_right_operationClosed
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSupport : OperationSupported (n := n) adj step)
    (hPort : OperationClosed step (L ∩ R)) :
    OperationClosed step R := by
  have hNoCrossSwap :
      ∀ ⦃a b⦄, a ∈ R \ L → b ∈ L \ R → ¬ adj a b := by
    intro a b ha hb hab
    exact hNoCross hb ha (hSymm hab)
  have hCoverSwap : R ∪ L = Set.univ := by
    simpa only [Set.union_comm] using hCover
  have hPortSwap : OperationClosed step (R ∩ L) := by
    simpa only [Set.inter_comm] using hPort
  exact old_left_operationClosed
    (L := R) (R := L) hCoverSwap hNoCrossSwap hSupport hPortSwap

/-- For a supported operation, any value whose inputs include one
left-private and one right-private vertex must belong to the port. -/
theorem mixed_operation_output_mem_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSupport : OperationSupported (n := n) adj step)
    (args : Fin n → W) (z : W) (hz : step args z)
    (i j : Fin n)
    (hi : args i ∈ L \ R)
    (hj : args j ∈ R \ L) :
    z ∈ L ∩ R := by
  exact cross_common_neighbour_mem_port hCover hNoCross hSymm hi hj
    (hSupport args z hz i) (hSupport args z hz j)

end CoherentPort
end StructuralRamsey.Girth
