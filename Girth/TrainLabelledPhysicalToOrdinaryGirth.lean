import Girth.LabelledWagonCutRestriction
import Girth.TrainRecursiveBottomEqualityBridge

set_option autoImplicit false
set_option Elab.async false

/-!
# Physical labelled bottom girth already implies ordinary A-support girth

A physical A-support edge is a set of vertices plus a proof that it
is an A-copy. Its subtype label is injectively determined by its
vertex carrier. Thus every ordinary Berge cycle of actual A-support
edges lifts, without identifying or discarding edges, to a labelled
cycle of the same length.

At the train's equality bottom cut, the quotient wagon labels are
exactly these physical A-support labels. Consequently the target's
*existing* labelled bottom wagon-girth assumption already implies
ordinary support girth at the SAME cutoff, as needed to construct
the initial forest stage. No additional ordinary-girth hypothesis.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA X : Type v}

/-- A labelled girth bound on all literal physical A-support
carriers implies the ordinary support hypergraph has that bound.
The reverse also holds for this faithful subtype edge labelling,
but is not required here. -/
theorem ordinaryGirth_of_labelledPhysicalASupport
    (A : RelStructure L UA) (B : RelStructure L X)
    (q : ℕ)
    (hLabelled : LabelledGirthGT
      (fun edge : OldACarrierEdge A B => edge.1) q) :
    GirthGT (supportCopies A B) q := by
  rintro ⟨c, hBound⟩
  let lifted : LabelledBergeCycle
      (fun edge : OldACarrierEdge A B => edge.1) := {
    length := c.length
    hlength := c.hlength
    label := fun i => ⟨c.edge i, c.edge_mem i⟩
    vertex := c.vertex
    label_injective := by
      intro i j hij
      apply c.edge_injective
      exact congrArg Subtype.val hij
    vertex_injective := c.vertex_injective
    left_mem := c.left_mem
    right_mem := c.right_mem
  }
  exact hLabelled ⟨lifted, hBound⟩

/-- The target's genuine BOTTOM labelled wagon girth supplies the
ordinary A-support girth needed by the initial picture. The bottom
edge partition is equality, so no wagon-index injection is lost. -/
theorem ordinaryGirth_of_targetBottomLabelledCut
    (A : RelStructure L UA) (B : RelStructure L X)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A B) m)
    (q : ℕ)
    (hBottom : LabelledGirthGT
      (T.wagonClassCarrier
        (fun edge : OldACarrierEdge A B => edge.1)
        (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))) q) :
    GirthGT (supportCopies A B) q := by
  have hEq :
      T.wagonClassCarrier
        (fun edge : OldACarrierEdge A B => edge.1)
        (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) =
        fun p => (T.bottomQuotientEdge p).1 :=
    T.bottom_wagonClassCarrier_eq (fun edge : OldACarrierEdge A B => edge.1)
  rw [hEq] at hBottom
  have hPhysical : LabelledGirthGT
      (fun edge : OldACarrierEdge A B => edge.1) q := by
    rintro ⟨c, hc⟩
    let lift : LabelledBergeCycle (fun p => (T.bottomQuotientEdge p).1) := {
      length := c.length
      hlength := c.hlength
      label := fun i =>
        Quotient.mk
          (T.wagonSetoid (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)))
          (c.label i)
      vertex := c.vertex
      label_injective := by
        intro i j h
        apply c.label_injective
        have hLabels :=
          congrArg T.bottomQuotientEdge h
        simpa using hLabels
      vertex_injective := c.vertex_injective
      left_mem := by
        intro i
        simpa using c.left_mem i
      right_mem := by
        intro i
        simpa using c.right_mem i
    }
    exact hBottom ⟨lift, hc⟩
  exact ordinaryGirth_of_labelledPhysicalASupport A B q hPhysical

end StructuralRamsey.Girth
