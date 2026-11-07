import Girth.TrainRecursiveInitialTailGirth
import Girth.TrainFillingIndexedContractedCarriers

set_option Elab.async false

/-!
# Labelled girth of heterogeneous dependent tagged choice unions

The actual G0 uses a DEPENDENT disjoint union of vertex sets:
  Σ c : C, (U c).Vertex.
The private-vertex type of U c can differ with the choice c. Thus
the ordinary tagged-girth lemma for I × V with a fixed vertex type
is not directly applicable.

A labelled Berge cycle of the tagged union cannot cross components:
each incidence forces the component tag of the edge label to equal
the tag of the incident vertex; cyclic adjacency makes all labels
have the same tag. We project the cycle into that one dependent fibre.

This proves a quantitative GIRTH bound while retaining every physical
edge label even if several labels share one carrier. It is not a
pruning argument or an output system-girth theorem.

The final corollary applies to the full physical first-wagon carrier
family of heterogeneous G0. This is a valid piece of the shortened
train's bottom-cut girth once its genuine individual choice components
have the required old local cut bound. Higher cut quotients and
the final Ramsey arrow are separate obligations.
-/

namespace StructuralRamsey.Girth

universe v
variable {C Q : Type v} {V : C → Type v}

/-- Inject one local vertex into its genuine dependent component. -/
def dependentTagVertex (c : C) (x : V c) : Sigma V := ⟨c, x⟩

theorem dependentTagVertex_injective (c : C) :
    Function.Injective (dependentTagVertex (V := V) c) := by
  intro x y h
  cases h
  rfl

/-- Full carriers in a heterogeneous labelled union, retaining BOTH
choice and wagon labels. No two labels are identified. -/
def dependentTaggedCarriers
    (H : ∀ c : C, Q → Set (V c)) (cq : C × Q) :
    Set (Sigma V) :=
  (dependentTagVertex (V := V) cq.1) '' H cq.1 cq.2

/-- Membership in a tagged fibre is exactly membership of its
underlying local vertex in the local carrier family. -/
theorem dependentTaggedCarriers_mem_fiber
    (H : ∀ c : C, Q → Set (V c))
    (c d : C) (q : Q) (hcd : c = d)
    (x : V d)
    (hx : dependentTagVertex (V := V) d x ∈
      dependentTaggedCarriers H (c, q)) :
    x ∈ H d q := by
  subst c
  obtain ⟨y, hy, hEq⟩ := hx
  have hxy : y = x := dependentTagVertex_injective d hEq
  simpa only [hxy] using hy

/-- If every individual choice has labelled girth greater than g,
the entire dependent Sigma union does as well. The conclusion is
meaningful even when C, Q, or individual V c are empty. -/
theorem labelledGirthGT_dependentTagged
    (H : ∀ c : C, Q → Set (V c))
    (g : ℕ)
    (hLocal : ∀ c : C, LabelledGirthGT (H c) g) :
    LabelledGirthGT (dependentTaggedCarriers H) g := by
  classical
  rintro ⟨cyc, hLen⟩
  have hLeftTag (i : Fin cyc.length) :
      (cyc.vertex i).1 = (cyc.label i).1 := by
    obtain ⟨x, _, hx⟩ := cyc.left_mem i
    exact (congrArg Sigma.fst hx).symm
  have hRightTag (i : Fin cyc.length) :
      (cyc.vertex i).1 = (cyc.label (cyclicSucc i)).1 := by
    obtain ⟨x, _, hx⟩ := cyc.right_mem i
    exact (congrArg Sigma.fst hx).symm
  let owner : Fin cyc.length → C := fun i => (cyc.label i).1
  have hStep (i : Fin cyc.length) :
      owner i = owner (cyclicSucc i) :=
    (hLeftTag i).symm.trans (hRightTag i)
  let zero : Fin cyc.length :=
    ⟨0, by have := cyc.hlength; omega⟩
  have hAll (i : Fin cyc.length) :
      owner i = owner (cyclicSucc zero) := by
    by_cases hi : i = zero
    · subst i
      exact hStep zero
    · exact cyclicOwner_eq_off_singleton cyc.hlength owner zero
        (fun j _ _ => hStep j) i hi
  have hLabelTag (i j : Fin cyc.length) :
      (cyc.label i).1 = (cyc.label j).1 :=
    (hAll i).trans (hAll j).symm
  let c0 : C := (cyc.label zero).1
  have hVertexTag (i : Fin cyc.length) :
      (cyc.vertex i).1 = c0 :=
    (hLeftTag i).trans (hLabelTag i zero)
  have hVertexExists (i : Fin cyc.length) :
      ∃ x : V c0, dependentTagVertex (V := V) c0 x =
        cyc.vertex i := by
    cases hv : cyc.vertex i with
    | mk d x =>
        have hd : d = c0 := by
          simpa only [hv] using hVertexTag i
        subst d
        exact ⟨x, hv.symm⟩
  let point (i : Fin cyc.length) : V c0 :=
    Classical.choose (hVertexExists i)
  have point_eq (i : Fin cyc.length) :
      dependentTagVertex (V := V) c0 (point i) = cyc.vertex i :=
    Classical.choose_spec (hVertexExists i)
  let projected : LabelledBergeCycle (H c0) := {
    length := cyc.length
    hlength := cyc.hlength
    label := fun i => (cyc.label i).2
    vertex := point
    label_injective := by
      intro i j hij
      exact cyc.label_injective
        (Prod.ext (hLabelTag i j) hij)
    vertex_injective := by
      intro i j hij
      apply cyc.vertex_injective
      calc
        cyc.vertex i = dependentTagVertex (V := V) c0 (point i) :=
          (point_eq i).symm
        _ = dependentTagVertex (V := V) c0 (point j) :=
          congrArg (dependentTagVertex (V := V) c0) hij
        _ = cyc.vertex j := point_eq j
    left_mem := by
      intro i
      apply dependentTaggedCarriers_mem_fiber
        H (cyc.label i).1 c0 (cyc.label i).2
        (hLabelTag i zero) (point i)
      change dependentTagVertex (V := V) c0 (point i) ∈
        dependentTaggedCarriers H (cyc.label i)
      rw [point_eq i]
      exact cyc.left_mem i
    right_mem := by
      intro i
      apply dependentTaggedCarriers_mem_fiber
        H (cyc.label (cyclicSucc i)).1 c0
        (cyc.label (cyclicSucc i)).2
        (hLabelTag (cyclicSucc i) zero) (point i)
      change dependentTagVertex (V := V) c0 (point i) ∈
        dependentTaggedCarriers H (cyc.label (cyclicSucc i))
      rw [point_eq i]
      exact cyc.right_mem i
  }
  exact hLocal c0 ⟨projected, hLen⟩

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The entire physical contracted first-wagon labelled hypergraph
has girth greater than g whenever each individual choice's FULL
first-wagon family does. In particular, no additional short cycle
can arise by gluing choice components: they remain genuinely tagged
and disjoint even on their original old vertices. -/
theorem contractedCarrier_labelledGirthGT
    (g : ℕ)
    (hLocal : ∀ c : C,
      LabelledGirthGT
        (fun p : P => Set.range ((U c).place p)) g) :
    LabelledGirthGT (contractedCarrier U) g := by
  exact labelledGirthGT_dependentTagged
    (fun c p => Set.range ((U c).place p))
    g hLocal

end StructuralRamsey.Girth.IndexedPrivateChoice
