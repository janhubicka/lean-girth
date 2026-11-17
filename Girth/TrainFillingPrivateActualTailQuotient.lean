import Girth.TrainWagonClassRestriction
import Girth.TrainFillingPrivateActualWagonOwner

set_option Elab.async false

/-!
# The ACTUAL shorter train on original first-wagon quotient labels

An original train of height 1+m has its genuine first wagons at
old level 1. The shortened train required by the cutoff-two
construction has one edge for each such first wagon and height m.
Its relation at NEW level nu must be precisely the original
relation at OLD level nu+1.

These relations are well defined on original first-wagon
quotient labels because the old train levels are nested.
The new bottom equals the ORIGINAL first-wagon equivalence,
hence is equality of quotient labels; the new top is
universal. We do NOT postulate a separate shortened train
with externally supplied equivalence relations.

The generic quotient-tail constructor below is independent
of Ramsey inputs, selected embeddings, filling and girth
arguments. It identifies every relation on actual labelled
first-wagon representatives, not just one-way preservation.

The original train still must satisfy its first-wagon cut
girth and parameter conditions in order to conclude the
shortened private geometry. Those are separate input facts.

Draft candidate source; no Lean kernel/axiom check yet.
-/

namespace StructuralRamsey.Girth

universe v
variable {E : Type v}

/-- The first nontrivial wagon level of a height (m+1)
original train. This always exists, including m=0,
and becomes equality at the shortened train's new bottom. -/
def EdgeTrainLevels.firstWagonLevel (m : ℕ) :
    Fin ((m + 1) + 1) :=
  (0 : Fin (m + 1)).succ

/-- Actual first-wagon label type, retaining distinct
quotient classes even when their vertex carriers agree. -/
abbrev EdgeTrainLevels.FirstWagon
    {m : ℕ} (T : EdgeTrainLevels E (m + 1)) :=
  Quotient (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m))

/-- A new nu-relation between original first-wagon labels
holds when their actual representatives lie in the same
ORIGINAL (nu+1)-wagon. Existential representatives make
the definition independent of any arbitrary section of
the quotient. -/
def EdgeTrainLevels.tailRelation
    {m : ℕ} (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1))
    (p q : T.FirstWagon) : Prop :=
  ∃ a b : E,
    (Quotient.mk (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) a :
      T.FirstWagon) = p ∧
    (Quotient.mk (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) b :
      T.FirstWagon) = q ∧
    T.rel ν.succ a b

/-- The original first-wagon relation is contained in
every shifted older relation: level 1 ≤ nu+1. This is
the exact nesting fact needed to compare two different
representatives of the SAME quotient label. -/
theorem EdgeTrainLevels.firstWagon_rel_of_shift
    {m : ℕ} (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1)) {a b : E}
    (h : T.rel (EdgeTrainLevels.firstWagonLevel m) a b) :
    T.rel ν.succ a b := by
  exact T.nested
    (EdgeTrainLevels.firstWagonLevel m) ν.succ
    (by
      change 1 ≤ ν.val + 1
      omega) a b h

/-- The NEW true tail relation on quotient classes agrees
with the old (nu+1)-relation for ANY chosen old physical
edge representatives, not only specially selected ones.
It preserves AND reflects every shifted level. -/
theorem EdgeTrainLevels.tailRelation_mk_iff
    {m : ℕ} (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1)) (a b : E) :
    T.tailRelation ν
      (Quotient.mk (T.wagonSetoid
        (EdgeTrainLevels.firstWagonLevel m)) a)
      (Quotient.mk (T.wagonSetoid
        (EdgeTrainLevels.firstWagonLevel m)) b) ↔
    T.rel ν.succ a b := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hxa : T.rel (EdgeTrainLevels.firstWagonLevel m) x a :=
      Quotient.exact hx
    have hyb : T.rel (EdgeTrainLevels.firstWagonLevel m) y b :=
      Quotient.exact hy
    have hxaOld := T.firstWagon_rel_of_shift ν hxa
    have hybOld := T.firstWagon_rel_of_shift ν hyb
    exact (T.equivalent ν.succ).trans
      ((T.equivalent ν.succ).symm hxaOld)
      ((T.equivalent ν.succ).trans hxy hybOld)
  · intro hab
    exact ⟨a, b, rfl, rfl, hab⟩

/-- The shortened train of height m is obtained directly from
the ORIGINAL height-(1+m) train by contracting its actual
level-one wagon classes. Every positive old level is
preserved AND reflected, and the top is still shared.

This construction uses NO new relation or girth input. -/
def EdgeTrainLevels.tailQuotient
    {m : ℕ} (T : EdgeTrainLevels E (m + 1)) :
    EdgeTrainLevels T.FirstWagon m where
  rel := T.tailRelation
  equivalent := by
    intro ν
    refine ⟨?_, ?_, ?_⟩
    · intro p
      induction p using Quotient.inductionOn with
      | h a =>
          exact ⟨a, a, rfl, rfl,
            (T.equivalent ν.succ).refl a⟩
    · intro p q
      rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨b, a, hb, ha,
        (T.equivalent ν.succ).symm hab⟩
    · intro p q r
      rintro ⟨a, b, ha, hb, hab⟩
        ⟨b', c, hb', hc, hbc⟩
      have hbb' :
          Quotient.mk (T.wagonSetoid
            (EdgeTrainLevels.firstWagonLevel m)) b =
          Quotient.mk (T.wagonSetoid
            (EdgeTrainLevels.firstWagonLevel m)) b' :=
        hb.trans hb'.symm
      have hbbOld :
          T.rel ν.succ b b' :=
        T.firstWagon_rel_of_shift ν (Quotient.exact hbb')
      exact ⟨a, c, ha, hc,
        (T.equivalent ν.succ).trans hab
          ((T.equivalent ν.succ).trans hbbOld hbc)⟩
  nested := by
    intro μ ν hμν p q
    rintro ⟨a, b, ha, hb, hab⟩
    refine ⟨a, b, ha, hb, ?_⟩
    exact T.nested μ.succ ν.succ
      (by
        change μ.val + 1 ≤ ν.val + 1
        omega) a b hab
  bottom := by
    intro p q
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      have hq :
          Quotient.mk (T.wagonSetoid
            (EdgeTrainLevels.firstWagonLevel m)) a =
          Quotient.mk (T.wagonSetoid
            (EdgeTrainLevels.firstWagonLevel m)) b :=
        Quotient.sound hab
      exact ha.symm.trans (hq.trans hb)
    · intro hp
      subst q
      induction p using Quotient.inductionOn with
      | h a =>
          exact ⟨a, a, rfl, rfl,
            (T.equivalent (EdgeTrainLevels.firstWagonLevel m)).refl a⟩
  top := by
    intro p q
    induction p using Quotient.inductionOn with
    | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
        refine ⟨a, b, rfl, rfl, ?_⟩
        have hTopIndex :
            (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)).succ =
              (⟨m + 1, Nat.lt_succ_self (m + 1)⟩ :
                Fin ((m + 1) + 1)) := by
          apply Fin.ext
          rfl
        rw [hTopIndex]
        exact T.top a b

/-- The actual tail train relation on physical original
first-wagon class labels is EXACTLY the old shifted
train relation between ANY representative original edges. -/
theorem EdgeTrainLevels.tailQuotient_rel_mk_iff
    {m : ℕ} (T : EdgeTrainLevels E (m + 1))
    (ν : Fin (m + 1)) (a b : E) :
    (T.tailQuotient).rel ν
      (Quotient.mk (T.wagonSetoid
        (EdgeTrainLevels.firstWagonLevel m)) a)
      (Quotient.mk (T.wagonSetoid
        (EdgeTrainLevels.firstWagonLevel m)) b) ↔
    T.rel ν.succ a b :=
  T.tailRelation_mk_iff ν a b


/-- The complete original vertex carrier of a shortened
wagon at new level nu equals LITERALLY the complete carrier
of its corresponding original wagon at old level nu+1.

Left: start with true first-wagon classes; collect their
complete original edge carriers across the new tail relation.
Right: collect the original old physical edge carriers
directly across old relation nu+1. No vertex is lost or
introduced by contracting first-wagon labels.

This is the key preparation identity for shifting ALL
proper horizontal cut girth and train parameter bounds. -/
theorem EdgeTrainLevels.tailQuotient_wagonCarrier_eq
    {m : ℕ} {V : Type v}
    (T : EdgeTrainLevels E (m + 1))
    (edges : E → Set V)
    (ν : Fin (m + 1)) (a : E) :
    (T.tailQuotient).wagonCarrier
      (T.wagonClassCarrier edges
        (EdgeTrainLevels.firstWagonLevel m))
      ν (Quotient.mk
        (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) a)
    = T.wagonCarrier edges ν.succ a := by
  ext x
  constructor
  · rintro ⟨q, hTail, hx⟩
    induction q using Quotient.inductionOn with
    | h b =>
      have hAB : T.rel ν.succ a b :=
        (T.tailQuotient_rel_mk_iff ν a b).mp hTail
      change x ∈
        T.wagonCarrier edges (EdgeTrainLevels.firstWagonLevel m) b
        at hx
      obtain ⟨f, hBF, hfx⟩ := hx
      have hBF' : T.rel ν.succ b f :=
        T.firstWagon_rel_of_shift ν hBF
      exact ⟨f,
        (T.equivalent ν.succ).trans hAB hBF', hfx⟩
  · rintro ⟨b, hAB, hx⟩
    refine ⟨Quotient.mk
        (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) b,
      ?_, ?_⟩
    · exact (T.tailQuotient_rel_mk_iff ν a b).mpr hAB
    · change x ∈
        T.wagonCarrier edges (EdgeTrainLevels.firstWagonLevel m) b
      exact ⟨b,
        (T.equivalent (EdgeTrainLevels.firstWagonLevel m)).refl b,
        hx⟩

/-- The same carrier identity on the actual QUOTIENT wagon
label types, not just on chosen edge representatives.
This preserves repeated wagon labels rather than
silently collapsing them by equality of vertex sets. -/
theorem EdgeTrainLevels.tailQuotient_wagonClassCarrier_mk
    {m : ℕ} {V : Type v}
    (T : EdgeTrainLevels E (m + 1))
    (edges : E → Set V)
    (ν : Fin (m + 1)) (a : E) :
    (T.tailQuotient).wagonClassCarrier
      (T.wagonClassCarrier edges
        (EdgeTrainLevels.firstWagonLevel m))
      ν (Quotient.mk ((T.tailQuotient).wagonSetoid ν)
        (Quotient.mk
          (T.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) a))
    =
    T.wagonClassCarrier edges ν.succ
      (Quotient.mk (T.wagonSetoid ν.succ) a) :=
  T.tailQuotient_wagonCarrier_eq edges ν a

end StructuralRamsey.Girth
