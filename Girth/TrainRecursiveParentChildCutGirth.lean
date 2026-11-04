import Girth.TrainRecursiveRefinementGlobalCutGirth

set_option autoImplicit false
set_option Elab.async false

/-!
# A quantitative parent-and-children lemma for labelled wagon-cut girth

At a finer train cut μ, the quotient wagon labels partition into
fibres over their parent quotient labels at a coarser cut ν.

If the COMPLETE parent cut has labelled girth >q, a child-labelled
Berge cycle of length ≤q cannot visit two parent labels. Its
parent-change connectors would yield a cyclic incidence circuit in
the finite subfamily of used parent carriers. (This is the same
raw cyclic-incidence compression already checked in the global
refinement girth-gain proof.) Thus it is entirely inside ONE genuine
parent fibre. If each such fibre's child cut has labelled girth >q,
no child cycle exists.

The conclusion is global labelled girth at μ, with no assumption
that the parent classes are connected, no quotienting of different
wagons with identical carriers, and no pruning of physical A-edges.
In particular, this is exactly the missing downward direction:
parent global cut + ALL parent-local child cuts => child global cut.

It does not derive the initial parent's global girth from local
child bounds alone; that base case is a separate target-cut input.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W : Type v}

/-- Global labelled girth descends one train cut when the parent
wagon cut has that girth and EVERY parent fibre of child wagons
has the same local labelled girth. Complete physical support and
all quotient labels remain explicit. -/
theorem EdgeTrainLevels.labelledCutGirth_of_parent_and_children
    {m : ℕ}
    (T : EdgeTrainLevels E m)
    (edge : E → Set W)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (q : ℕ) (hq : 2 ≤ q)
    (hParent :
      LabelledGirthGT (T.wagonClassCarrier edge ν) q)
    (hChildren : ∀ p : Quotient (T.wagonSetoid ν),
      LabelledGirthGT
        (fun a : {a : Quotient (T.wagonSetoid μ) //
          T.wagonParent μ ν hμν a = p} =>
          T.wagonClassCarrier edge μ a.val) q) :
    LabelledGirthGT (T.wagonClassCarrier edge μ) q := by
  classical
  have hIntoParent (a : Quotient (T.wagonSetoid μ)) :
      T.wagonClassCarrier edge μ a ⊆
        T.wagonClassCarrier edge ν (T.wagonParent μ ν hμν a) := by
    induction a using Quotient.inductionOn with
    | h e =>
        change T.wagonCarrier edge μ e ⊆ T.wagonCarrier edge ν e
        rintro x ⟨f, hef, hxf⟩
        exact ⟨f, T.nested μ ν hμν e f hef, hxf⟩
  rintro ⟨C, hLength⟩
  let owner : Fin C.length → Quotient (T.wagonSetoid ν) :=
    fun i => T.wagonParent μ ν hμν (C.label i)
  have hConstant : ∀ i j : Fin C.length, owner i = owner j := by
    by_contra h
    push Not at h
    obtain ⟨i, j, hij⟩ := h
    let Used : Type v := Set.range owner
    let picked : Fin C.length → Used :=
      fun k => ⟨owner k, ⟨k, rfl⟩⟩
    have hOnto : Function.Surjective picked := by
      rintro ⟨p, ⟨k, hk⟩⟩
      exact ⟨k, Subtype.ext hk⟩
    haveI : Finite Used := Finite.of_surjective picked hOnto
    letI : Fintype Used := Fintype.ofFinite Used
    have hCard : Fintype.card Used ≤ q := by
      have hc : Fintype.card Used ≤ Fintype.card (Fin C.length) :=
        Fintype.card_le_of_surjective picked hOnto
      have hc' : Fintype.card Used ≤ C.length := by simpa using hc
      exact hc'.trans hLength
    let carrier : Used → Set W :=
      fun p => T.wagonClassCarrier edge ν p.val
    have hUsedGirth : LabelledGirthGT carrier q :=
      labelledGirthGT_of_injective_reindex
        (T.wagonClassCarrier edge ν)
        Subtype.val Subtype.val_injective q hParent
    have hAcyclic : (boundaryIncidenceGraph carrier).IsAcyclic :=
      labelledGirthGT_incidence_acyclic_of_card
        carrier q hq hCard hUsedGirth
    have hBoundary :
        ∀ k, picked k ≠ picked (cyclicSucc k) →
          C.vertex k ∈ carrier (picked k) ∧
          C.vertex k ∈ carrier (picked (cyclicSucc k)) := by
      intro k _
      constructor
      · exact hIntoParent (C.label k) (C.left_mem k)
      · exact hIntoParent (C.label (cyclicSucc k)) (C.right_mem k)
    let raw : RawCyclicIncidenceData carrier := {
      length := C.length
      hlength := C.hlength
      label := picked
      connector := C.vertex
      connector_injective := C.vertex_injective
      boundary_mem := hBoundary
      nonconstant := ⟨i, j, fun heq =>
        hij (congrArg Subtype.val heq)⟩
    }
    exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic
      hAcyclic raw.compress
  let zero : Fin C.length := ⟨0, by have := C.hlength; omega⟩
  let parent : Quotient (T.wagonSetoid ν) := owner zero
  let child : Fin C.length →
      {a : Quotient (T.wagonSetoid μ) //
        T.wagonParent μ ν hμν a = parent} :=
    fun i => ⟨C.label i, hConstant i zero⟩
  let lifted : LabelledBergeCycle
      (fun a : {a : Quotient (T.wagonSetoid μ) //
        T.wagonParent μ ν hμν a = parent} =>
        T.wagonClassCarrier edge μ a.val) := {
    length := C.length
    hlength := C.hlength
    label := child
    vertex := C.vertex
    label_injective := by
      intro i j hij
      exact C.label_injective (congrArg Subtype.val hij)
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem
  }
  exact hChildren parent ⟨lifted, hLength⟩

end StructuralRamsey.Girth
