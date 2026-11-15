import Girth.TrainFillingPrivateActualTailQuotient
import Girth.TrainWagonQuotientTransport
import Girth.LabelledWagonCutRestriction

set_option Elab.async false

/-!
# Exact original vs first-wagon-contracted quotient wagon labels

At source height 1+m, the shortened train on the genuine
level-one wagon classes is the tailQuotient of the
original EdgeTrainLevels T.

A wagon class at shortened level nu is an equivalence
class of first-wagon equivalence classes. Because
old level-one equivalence is finer than every old
level nu+1, this quotient-of-quotient is CANONICALLY
equivalent to the true original wagon class at nu+1.

The equivalence and carrier equality below retain ALL
wagon labels, including different labels with equal
vertex carriers. No set-of-carriers reindex that might
silently identify duplicates is used.

The companion labelled-girth transfer will use this
equivalence rather than falsely assuming wagon girth
is automatically preserved under an arbitrary quotient.

Uncompiled Lean source candidate; no output girth is
assumed or claimed.
-/

namespace StructuralRamsey.Girth

universe v
variable {E : Type v}

/-- Exact bijection from the ACTUAL shortened nu-wagon
quotient labels to the original old (nu+1)-wagon
quotient labels, using only nested source train data. -/
noncomputable def EdgeTrainLevels.tailWagonClassEquiv
    {m : ℕ} (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1)) :
    Quotient ((T.tailQuotient).wagonSetoid ν) ≃
      Quotient (T.wagonSetoid ν.succ) where
  toFun := fun q => Quotient.liftOn q
    (fun p : T.FirstWagon =>
      Quotient.liftOn p
        (fun a : E => Quotient.mk (T.wagonSetoid ν.succ) a)
        (by
          intro a b hab
          exact Quotient.sound (T.firstWagon_rel_of_shift ν hab)))
    (by
      intro p q h
      induction p using Quotient.inductionOn with
      | h a =>
        induction q using Quotient.inductionOn with
        | h b =>
          exact Quotient.sound
            ((T.tailQuotient_rel_mk_iff ν a b).mp h))
  invFun := fun q => Quotient.liftOn q
    (fun a : E => Quotient.mk ((T.tailQuotient).wagonSetoid ν)
        (Quotient.mk
          (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) a))
    (by
      intro a b hab
      exact Quotient.sound
        ((T.tailQuotient_rel_mk_iff ν a b).mpr hab))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h p =>
      induction p using Quotient.inductionOn with
      | h a =>
        rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      rfl

/-- The two labelled quotient wagon classes have LITERALLY
the same complete original vertex carrier, for every
old cut nu+1. This extends the representative version
of tailQuotient_wagonCarrier_eq to ALL quotient labels. -/
theorem EdgeTrainLevels.tailWagonClassEquiv_carrier
    {m : ℕ} {V : Type v}
    (T : EdgeTrainLevels E (m + 1))
    (edges : E → Set V)
    (ν : Fin (m + 1))
    (q : Quotient ((T.tailQuotient).wagonSetoid ν)) :
    (T.tailQuotient).wagonClassCarrier
        (T.wagonClassCarrier edges
          (EdgeTrainLevels.firstWagonLevel m))
        ν q =
      T.wagonClassCarrier edges ν.succ
        (T.tailWagonClassEquiv ν q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    induction p using Quotient.inductionOn with
    | h a =>
      exact T.tailQuotient_wagonClassCarrier_mk edges ν a

/-- Every original wagon is the shifted image of exactly
one shortened wagon, with NO labels lost, duplicated or
collapsed. This is the precise parent-label interface
needed by shifted train parameter bounds and labelled
horizontal cut girth. -/
theorem EdgeTrainLevels.tailWagonClassEquiv_surjective
    {m : ℕ}
    (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1)) :
    Function.Surjective (T.tailWagonClassEquiv ν) :=
  (T.tailWagonClassEquiv ν).surjective


/-- LABELLED wagon girth of the genuine shortened train at
level nu is EQUIVALENT to labelled girth of the ORIGINAL
train at level nu+1. This is an exact transport through
a bijection of wagon labels with literally equal carriers;
it is not a claim about unlabelled sets of wagon vertices.

In particular the paper's original tail girth bounds
shift one place with NO loss of girth, and no extra
assumption on the shortened quotient train is needed. -/
theorem EdgeTrainLevels.tailQuotient_labelledCutGirth_iff
    {m : ℕ} {V : Type v}
    (T : EdgeTrainLevels E (m + 1))
    (edges : E → Set V)
    (ν : Fin (m + 1)) (g : ℕ) :
    LabelledGirthGT
      ((T.tailQuotient).wagonClassCarrier
        (T.wagonClassCarrier edges
          (EdgeTrainLevels.firstWagonLevel m)) ν) g ↔
    LabelledGirthGT
      (T.wagonClassCarrier edges ν.succ) g := by
  let eqv := T.tailWagonClassEquiv ν
  let old := T.wagonClassCarrier edges ν.succ
  let reduced := (T.tailQuotient).wagonClassCarrier
    (T.wagonClassCarrier edges
      (EdgeTrainLevels.firstWagonLevel m)) ν
  have hExact : ∀ q, reduced q = old (eqv q) :=
    T.tailWagonClassEquiv_carrier edges ν
  have hOldToNew : ∀ q, old q ⊆ reduced (eqv.symm q) := by
    intro q
    have h := hExact (eqv.symm q)
    rw [eqv.apply_symm_apply] at h
    rw [h]
  have hNewToOld : ∀ q, reduced q ⊆ old (eqv q) := by
    intro q
    rw [hExact]
  constructor
  · intro hShort
    exact labelledGirthGT_of_injective_shrinking
      reduced old eqv.symm eqv.symm.injective
      hOldToNew g hShort
  · intro hOriginal
    exact labelledGirthGT_of_injective_shrinking
      old reduced eqv eqv.injective
      hNewToOld g hOriginal

end StructuralRamsey.Girth
