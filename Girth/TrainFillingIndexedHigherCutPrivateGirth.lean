import Girth.TrainFillingIndexedDependentTaggedGirth
import Girth.TrainWagonClassRestriction

set_option Elab.async false

/-!
# Higher-cut wagon girth of actual heterogeneous private extensions

At any fixed proper cut μ, a new private vertex (p,x) occurs in just
ONE quotient wagon: the one containing its first-wagon owner p.
Thus two DISTINCT quotient wagons can meet only on OLD vertices.

A labelled Berge cycle in the expanded μ-wagon carrier family has
distinct consecutive quotient labels. Its connecting vertices must
therefore be old. Projecting them gives a short labelled cycle in
the original μ-wagon carrier family, without shrinking or deleting
any physical edge labels.

The dependent tagged-girth theorem for the full choice union then
lifts every one-choice higher-cut bound to all of heterogeneous G0.

This is precisely a quantitative higher CUT-girth transfer for the
contracted G0 train. It retains quotient occurrence labels and a
single global top is treated separately; it does not assert the
more delicate A2/A3 system-girth or the final Ramsey arrow.
-/

namespace StructuralRamsey.Girth

universe v
variable {V Z Q : Type v}

/-- Adding private vertices cannot create a short labelled cycle if
old vertex incidence is unchanged and each private point belongs
to at most ONE labelled carrier. -/
theorem labelledGirthGT_of_unique_private
    (old : Q → Set V) (expanded : Q → Set (V ⊕ Z))
    (hOld : ∀ q : Q, ∀ x : V,
      Sum.inl x ∈ expanded q ↔ x ∈ old q)
    (hPrivate : ∀ q r : Q, ∀ z : Z,
      Sum.inr z ∈ expanded q →
      Sum.inr z ∈ expanded r → q = r)
    (g : ℕ)
    (hGirth : LabelledGirthGT old g) :
    LabelledGirthGT expanded g := by
  classical
  rintro ⟨cyc, hg⟩
  have hSuccNe (i : Fin cyc.length) : i ≠ cyclicSucc i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = (i.val + 1) % cyc.length at hv
    have hn := cyc.hlength
    have hi := i.isLt
    by_cases hlt : i.val + 1 < cyc.length
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have hlast : i.val + 1 = cyc.length := by omega
      rw [hlast, Nat.mod_self] at hv
      omega
  have hDistinct (i : Fin cyc.length) :
      cyc.label i ≠ cyc.label (cyclicSucc i) := by
    intro h
    exact hSuccNe i (cyc.label_injective h)
  have hOldPoint (i : Fin cyc.length) :
      ∃ x : V, cyc.vertex i = Sum.inl x := by
    cases hv : cyc.vertex i with
    | inl x =>
        exact ⟨x, hv.symm⟩
    | inr z =>
        have hl : Sum.inr z ∈ expanded (cyc.label i) := by
          rw [← hv]
          exact cyc.left_mem i
        have hr : Sum.inr z ∈
            expanded (cyc.label (cyclicSucc i)) := by
          rw [← hv]
          exact cyc.right_mem i
        exact False.elim (hDistinct i
          (hPrivate (cyc.label i) (cyc.label (cyclicSucc i)) z hl hr))
  let vertex (i : Fin cyc.length) : V :=
    Classical.choose (hOldPoint i)
  have hVertex (i : Fin cyc.length) :
      cyc.vertex i = Sum.inl (vertex i) :=
    Classical.choose_spec (hOldPoint i)
  let projected : LabelledBergeCycle old := {
    length := cyc.length
    hlength := cyc.hlength
    label := cyc.label
    vertex := vertex
    label_injective := cyc.label_injective
    vertex_injective := by
      intro i j hij
      apply cyc.vertex_injective
      calc
        cyc.vertex i = Sum.inl (vertex i) := hVertex i
        _ = Sum.inl (vertex j) := congrArg Sum.inl hij
        _ = cyc.vertex j := (hVertex j).symm
    left_mem := by
      intro i
      apply (hOld (cyc.label i) (vertex i)).mp
      rw [← hVertex i]
      exact cyc.left_mem i
    right_mem := by
      intro i
      apply (hOld (cyc.label (cyclicSucc i)) (vertex i)).mp
      rw [← hVertex i]
      exact cyc.right_mem i
  }
  exact hGirth ⟨projected, hg⟩

namespace PrivateWagonInput

variable {P X : Type v}
variable (U : PrivateWagonInput V P X)

/-- Exact old-vertex membership at every actual quotient wagon cut.
Private extensions preserve all original old incidence. -/
theorem expandedWagonClass_old_iff
    {m : ℕ} (T : EdgeTrainLevels P m)
    (μ : Fin (m + 1))
    (q : Quotient (T.wagonSetoid μ)) (x : V) :
    Sum.inl x ∈
      T.wagonClassCarrier (fun p => Set.range (U.place p)) μ q ↔
    x ∈ T.wagonClassCarrier U.oldCarrier μ q := by
  induction q using Quotient.inductionOn with
  | h p =>
      change (∃ b : P, T.rel μ p b ∧
          Sum.inl x ∈ Set.range (U.place b)) ↔
        (∃ b : P, T.rel μ p b ∧ x ∈ U.oldCarrier b)
      constructor
      · rintro ⟨b, hpb, hx⟩
        exact ⟨b, hpb, (U.old_mem_range b x).mp hx⟩
      · rintro ⟨b, hpb, hx⟩
        exact ⟨b, hpb, (U.old_mem_range b x).mpr hx⟩

/-- A private point may belong to many first-wagon occurrences in
its same quotient class, but to exactly ONE QUOTIENT WAGON label:
the class containing its actual first-wagon owner. -/
theorem expandedWagonClass_private_unique
    {m : ℕ} (T : EdgeTrainLevels P m)
    (μ : Fin (m + 1))
    (q r : Quotient (T.wagonSetoid μ)) (z : U.PrivateVertex)
    (hq : Sum.inr z ∈
      T.wagonClassCarrier (fun p => Set.range (U.place p)) μ q)
    (hr : Sum.inr z ∈
      T.wagonClassCarrier (fun p => Set.range (U.place p)) μ r) :
    q = r := by
  induction q using Quotient.inductionOn with
  | h p =>
      induction r using Quotient.inductionOn with
      | h s =>
          change (∃ b : P, T.rel μ p b ∧
              Sum.inr z ∈ Set.range (U.place b)) at hq
          change (∃ d : P, T.rel μ s d ∧
              Sum.inr z ∈ Set.range (U.place d)) at hr
          obtain ⟨b, hpb, x, hxb⟩ := hq
          obtain ⟨d, hsd, y, hyd⟩ := hr
          have hb : b = z.1.1 :=
            U.place_eq_private_owner b x z hxb
          have hd : d = z.1.1 :=
            U.place_eq_private_owner d y z hyd
          have hbd : b = d := hb.trans hd.symm
          subst d
          exact Quotient.sound ((T.equivalent μ).trans hpb
            ((T.equivalent μ).symm hsd))

/-- The expanded physical μ-wagon family inherits its FULL original
labelled μ-cut girth, with no independent girth assumption on X. -/
theorem expandedWagonClass_labelledGirthGT
    {m : ℕ} (T : EdgeTrainLevels P m)
    (μ : Fin (m + 1)) (g : ℕ)
    (hOld : LabelledGirthGT
      (T.wagonClassCarrier U.oldCarrier μ) g) :
    LabelledGirthGT
      (T.wagonClassCarrier
        (fun p => Set.range (U.place p)) μ) g :=
  labelledGirthGT_of_unique_private
    (T.wagonClassCarrier U.oldCarrier μ)
    (T.wagonClassCarrier (fun p => Set.range (U.place p)) μ)
    (fun q x => U.expandedWagonClass_old_iff T μ q x)
    (fun q r z => U.expandedWagonClass_private_unique T μ q r z)
    g hOld

end PrivateWagonInput

namespace IndexedPrivateChoice

variable {C P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Exact quantitative girth of the tagged full μ-wagon cut over
ALL heterogeneous choices, inherited only from the original old
μ-wagon quotient carriers of each choice. The labels are literally
(choice, actual quotient wagon), not mere sets of carriers. -/
theorem indexedExpandedProperCut_labelledGirthGT
    {m : ℕ} (T : EdgeTrainLevels P m)
    (μ : Fin (m + 1)) (g : ℕ)
    (hOld : ∀ c : C,
      LabelledGirthGT
        (T.wagonClassCarrier (U c).oldCarrier μ) g) :
    LabelledGirthGT
      (dependentTaggedCarriers
        (fun c => T.wagonClassCarrier
          (fun p => Set.range ((U c).place p)) μ)) g := by
  apply labelledGirthGT_dependentTagged
  intro c
  exact PrivateWagonInput.expandedWagonClass_labelledGirthGT
    (U c) T μ g (hOld c)

end IndexedPrivateChoice
end StructuralRamsey.Girth
