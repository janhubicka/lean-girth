import Girth.TrainRecursiveRefinement

set_option Elab.async false
set_option autoImplicit false

/-!
# The appended first-refinement partitions and their actual labels

An old refinement is copied into each standard on the edge product `I × E`.
Its last lower cut consists of standard-labelled old first wagons.  The
next cut is the actual output first relation, and every higher output
relation is retained.  Exact restriction at the first cut gives nesting
and shows that two children of one new parent have different standard
owners.  All maps below act on actual quotient wagon labels.
-/

namespace StructuralRamsey.Girth.FirstRefinementAppend

universe v
variable {E I W Z : Type v} {m d : ℕ}

/-- The lower cut with the same index in the appended train. -/
def lowIndex (m d : ℕ) (_hm : 0 < m) (μ : Fin (d + 2)) :
    Fin (m + (d + 1) + 1) := ⟨μ.val, by have := μ.isLt; omega⟩

/-- The corresponding cut of the old refined train. -/
def oldLowIndex (m d : ℕ) (hm : 0 < m) (μ : Fin (d + 2)) :
    Fin (m + d + 1) := ⟨μ.val, by have := μ.isLt; omega⟩

/-- The appended parent cut, representing the output first relation. -/
def freshParentIndex (m d : ℕ) (hm : 0 < m) :
    Fin (m + (d + 1) + 1) := ⟨d + 2, by omega⟩

variable (hm : 0 < m)
variable (V : EdgeTrainLevels E (m + d))
variable (U : EdgeTrainLevels (I × E) m)
variable (hFirst : ∀ (i : I) (a b : E),
  V.rel (oldLowIndex m d hm (Fin.last (d + 1))) a b ↔
    U.rel ⟨1, by omega⟩ (i, a) (i, b))

/-- Retain the disjoint standard refinements below the actual output
first relation, and retain every higher output relation after the shift. -/
def train : EdgeTrainLevels (I × E) (m + (d + 1)) where
  rel μ a b := if h : μ.val ≤ d + 1 then
      a.1 = b.1 ∧ V.rel ⟨μ.val, by have := μ.isLt; omega⟩ a.2 b.2
    else U.rel ⟨μ.val - (d + 1), by have := μ.isLt; omega⟩ a b
  equivalent := by
    intro μ
    by_cases h : μ.val ≤ d + 1
    · simp only [dite_eq_left h]
      exact ⟨fun a => ⟨rfl, (V.equivalent _).refl a.2⟩,
        fun hab => ⟨hab.1.symm, (V.equivalent _).symm hab.2⟩,
        fun hab hbc => ⟨hab.1.trans hbc.1, (V.equivalent _).trans hab.2 hbc.2⟩⟩
    · simp only [dite_eq_right h]
      exact U.equivalent _
  nested := by
    intro μ ν hμν a b hab
    by_cases hμ : μ.val ≤ d + 1
    · rw [dite_eq_left hμ] at hab
      by_cases hν : ν.val ≤ d + 1
      · rw [dite_eq_left hν]
        exact ⟨hab.1, V.nested _ _ hμν a.2 b.2 hab.2⟩
      · rw [dite_eq_right hν]
        have hOld : V.rel (oldLowIndex m d hm (Fin.last (d + 1))) a.2 b.2 :=
          V.nested _ _ (by change μ.val ≤ d + 1; exact hμ) a.2 b.2 hab.2
        have hOut : U.rel ⟨1, by omega⟩ a b := by
          rcases a with ⟨i, a⟩
          rcases b with ⟨j, b⟩
          have hij : i = j := hab.1
          subst j
          exact (hFirst i a b).mp hOld
        exact U.nested _ _ (by change 1 ≤ ν.val - (d + 1); omega) a b hOut
    · rw [dite_eq_right hμ] at hab
      have hν : ¬ ν.val ≤ d + 1 := by
        change μ.val ≤ ν.val at hμν
        omega
      rw [dite_eq_right hν]
      exact U.nested _ _ (Nat.sub_le_sub_right hμν (d + 1)) a b hab
  bottom := by
    intro a b
    change (a.1 = b.1 ∧ V.rel ⟨0, by omega⟩ a.2 b.2) ↔ a = b
    rw [V.bottom]
    exact Prod.ext_iff.symm
  top := by
    intro a b
    rw [dite_eq_right (by omega : ¬ m + (d + 1) ≤ d + 1)]
    have hTop : (⟨m + (d + 1) - (d + 1), by omega⟩ : Fin (m + 1)) =
        ⟨m, Nat.lt_succ_self m⟩ := by
      apply Fin.ext
      change m + (d + 1) - (d + 1) = m
      omega
    rw [hTop]
    exact U.top a b

/-- The lower train relation keeps the standard index and exactly the
old refined relation. -/
theorem lower_rel (μ : Fin (d + 2)) (a b : I × E) :
    (train hm V U hFirst).rel (lowIndex m d hm μ) a b ↔
      a.1 = b.1 ∧ V.rel (oldLowIndex m d hm μ) a.2 b.2 := by
  dsimp only [train, lowIndex, oldLowIndex]
  rw [dite_eq_left (by have := μ.isLt; omega)]

/-- Every positive output cut is retained, including the universal top. -/
theorem oldLevels (μ : Fin (m + 1)) (hμ : 0 < μ.val) (a b : I × E) :
    (train hm V U hFirst).rel
      (EdgeTrainLevels.firstRefinementShift m (d + 1) μ) a b ↔
        U.rel μ a b := by
  dsimp only [train, EdgeTrainLevels.firstRefinementShift]
  rw [dite_eq_right (by omega : ¬ μ.val + (d + 1) ≤ d + 1)]
  have hIndex : (⟨μ.val + (d + 1) - (d + 1), by have := μ.isLt; omega⟩ :
      Fin (m + 1)) = μ := by
    apply Fin.ext
    change μ.val + (d + 1) - (d + 1) = μ.val
    omega
  rw [hIndex]

/-- The fresh parent cut is exactly the output first equivalence. -/
theorem freshParent_rel (a b : I × E) :
    (train hm V U hFirst).rel (freshParentIndex m d hm) a b ↔
      U.rel ⟨1, by omega⟩ a b := by
  dsimp only [train, freshParentIndex]
  rw [dite_eq_right (by omega : ¬ d + 2 ≤ d + 1)]
  have hIndex : (⟨d + 2 - (d + 1), by omega⟩ : Fin (m + 1)) =
      ⟨1, by omega⟩ := by
    apply Fin.ext
    change d + 2 - (d + 1) = 1
    omega
  rw [hIndex]

/-- Exact lower quotient labels: a standard index and an old refined
wagon label.  Equal carrier sets are not identified. -/
def lowerWagonEquiv (μ : Fin (d + 2)) :
    Quotient ((train hm V U hFirst).wagonSetoid (lowIndex m d hm μ)) ≃
      I × Quotient (V.wagonSetoid (oldLowIndex m d hm μ)) where
  toFun := fun q => Quotient.liftOn q
    (fun a => (a.1, Quotient.mk (V.wagonSetoid (oldLowIndex m d hm μ)) a.2))
    (by
      intro a b hab
      have h := (lower_rel hm V U hFirst μ a b).mp hab
      exact Prod.ext h.1 (Quotient.sound h.2))
  invFun := fun q => Quotient.liftOn q.2
    (fun a => Quotient.mk ((train hm V U hFirst).wagonSetoid (lowIndex m d hm μ))
      (q.1, a))
    (by
      intro a b hab
      exact Quotient.sound ((lower_rel hm V U hFirst μ (q.1, a) (q.1, b)).mpr
        ⟨rfl, hab⟩))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => rfl
  right_inv := by
    rintro ⟨i, q⟩
    induction q using Quotient.inductionOn with
    | h a => rfl

@[simp] theorem lowerWagonEquiv_mk (μ : Fin (d + 2)) (i : I) (a : E) :
    lowerWagonEquiv hm V U hFirst μ (Quotient.mk _ (i, a)) =
      (i, Quotient.mk (V.wagonSetoid (oldLowIndex m d hm μ)) a) := rfl

/-- The whole lower wagon carrier is exactly the standard image of its
old labelled carrier. -/
theorem lowerWagon_carrier (edge : E → Set W) (vertexMap : I → W → Z)
    (μ : Fin (d + 2))
    (a : Quotient ((train hm V U hFirst).wagonSetoid (lowIndex m d hm μ))) :
    (train hm V U hFirst).wagonClassCarrier
        (fun ie => vertexMap ie.1 '' edge ie.2) (lowIndex m d hm μ) a =
      vertexMap (lowerWagonEquiv hm V U hFirst μ a).1 ''
        V.wagonClassCarrier edge (oldLowIndex m d hm μ)
          (lowerWagonEquiv hm V U hFirst μ a).2 := by
  induction a using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨i, a⟩
      change (train hm V U hFirst).wagonCarrier
          (fun ie => vertexMap ie.1 '' edge ie.2) (lowIndex m d hm μ) (i, a) =
        vertexMap i '' V.wagonCarrier edge (oldLowIndex m d hm μ) a
      ext z
      constructor
      · rintro ⟨⟨j, b⟩, hab, x, hxb, hxz⟩
        have h := (lower_rel hm V U hFirst μ (i, a) (j, b)).mp hab
        change i = j ∧ _ at h
        obtain ⟨rfl, hOld⟩ := h
        exact ⟨x, ⟨b, hOld, hxb⟩, hxz⟩
      · rintro ⟨x, ⟨b, hab, hxb⟩, rfl⟩
        exact ⟨(i, b), (lower_rel hm V U hFirst μ (i, a) (i, b)).mpr
          ⟨rfl, hab⟩, x, hxb, rfl⟩

/-- Actual lower parent maps commute with the standard/old-wagon labels. -/
theorem lowerWagon_parent (μ ν : Fin (d + 2)) (hμν : μ ≤ ν)
    (a : Quotient ((train hm V U hFirst).wagonSetoid (lowIndex m d hm μ))) :
    lowerWagonEquiv hm V U hFirst ν
      ((train hm V U hFirst).wagonParent
        (lowIndex m d hm μ) (lowIndex m d hm ν) hμν a) =
      ((lowerWagonEquiv hm V U hFirst μ a).1,
        V.wagonParent (oldLowIndex m d hm μ) (oldLowIndex m d hm ν) hμν
          (lowerWagonEquiv hm V U hFirst μ a).2) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

/-- The standard owner of an actual child of one appended parent. -/
def freshChildOwner
    (p : Quotient ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm))) :
    {a : Quotient ((train hm V U hFirst).wagonSetoid
        (lowIndex m d hm (Fin.last (d + 1)))) //
      (train hm V U hFirst).wagonParent
        (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
        (by change d + 1 ≤ d + 2; omega) a = p} → I :=
  fun a => (lowerWagonEquiv hm V U hFirst (Fin.last (d + 1)) a.val).1

/-- Within one actual output-first parent, distinct new children have
distinct standard owners.  This is derived from exact train restriction. -/
theorem freshChildOwner_injective
    (p : Quotient ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm))) :
    Function.Injective (freshChildOwner hm V U hFirst p) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  change a = b
  revert ha hb hab
  induction a using Quotient.inductionOn with
  | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
          intro ha hb hab
          rcases a with ⟨i, a⟩
          rcases b with ⟨j, b⟩
          change i = j at hab
          subst j
          have hParent :
              (Quotient.mk ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm))
                (i, a)) = Quotient.mk _ (i, b) := ha.trans hb.symm
          have hOutput := (freshParent_rel hm V U hFirst (i, a) (i, b)).mp
            (Quotient.exact hParent)
          exact Quotient.sound ((lower_rel hm V U hFirst (Fin.last (d + 1))
            (i, a) (i, b)).mpr ⟨rfl, (hFirst i a b).mpr hOutput⟩)

end StructuralRamsey.Girth.FirstRefinementAppend
