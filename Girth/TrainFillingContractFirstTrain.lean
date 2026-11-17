import Girth.TrainWagonClassRestriction

set_option autoImplicit false

namespace StructuralRamsey.Girth.EdgeTrainLevels

universe v
variable {E V : Type v} {m : ℕ} (T : EdgeTrainLevels E (m + 1))

/-- The edges of the shortened train are the genuine original first
wagons. No quotient is taken by equality of their vertex carriers. -/
abbrev FirstWagon := Quotient (T.wagonSetoid (0 : Fin (m + 1)).succ)

private def contractFirstRel (μ : Fin (m + 1)) (a b : T.FirstWagon) : Prop :=
  Quotient.liftOn₂ a b (T.rel μ.succ) (by
    intro x y x' y' hx hy
    have hle : (0 : Fin (m + 1)).succ ≤ μ.succ := Nat.succ_le_succ (Nat.zero_le μ.val)
    have hx' := T.nested _ μ.succ hle x x' hx
    have hy' := T.nested _ μ.succ hle y y' hy
    let h := T.equivalent μ.succ
    exact propext ⟨fun hxy => h.trans (h.symm hx') (h.trans hxy hy'),
      fun hxy => h.trans hx' (h.trans hxy (h.symm hy'))⟩)

/-- Contract the original first wagons and retain every positive quotient
relation, removing only the original equality level. -/
def contractFirst : EdgeTrainLevels T.FirstWagon m where
  rel := T.contractFirstRel
  equivalent := by
    intro μ
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Quotient.inductionOn a (fun x => (T.equivalent μ.succ).refl x)
    · intro a b
      exact Quotient.inductionOn₂ a b (fun _ _ h => (T.equivalent μ.succ).symm h)
    · intro a b c
      exact Quotient.inductionOn₃ a b c (fun _ _ _ h₁ h₂ => (T.equivalent μ.succ).trans h₁ h₂)
  nested := by
    intro μ ν h a b
    exact Quotient.inductionOn₂ a b
      (fun x y hxy => T.nested μ.succ ν.succ (Nat.succ_le_succ h) x y hxy)
  bottom := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change T.rel (0 : Fin (m + 1)).succ x y ↔
      Quotient.mk (T.wagonSetoid (0 : Fin (m + 1)).succ) x =
        Quotient.mk (T.wagonSetoid (0 : Fin (m + 1)).succ) y
    exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  top := by
    intro a b
    exact Quotient.inductionOn₂ a b (fun x y => T.top x y)

/-- Literal first-wagon label of an original physical edge. -/
def firstWagon (e : E) : T.FirstWagon := Quotient.mk _ e

@[simp] theorem contractFirst_rel_firstWagon (μ : Fin (m + 1)) (a b : E) :
    T.contractFirst.rel μ (T.firstWagon a) (T.firstWagon b) ↔ T.rel μ.succ a b := Iff.rfl

/-- The shorter cut `μ` has exactly the original positive cut `μ.succ`
wagon labels, including the original universal top. -/
def contractFirstWagonEquiv (μ : Fin (m + 1)) :
    Quotient (T.contractFirst.wagonSetoid μ) ≃ Quotient (T.wagonSetoid μ.succ) where
  toFun := fun q => Quotient.liftOn q
    (fun p : T.FirstWagon => Quotient.liftOn p (Quotient.mk (T.wagonSetoid μ.succ)) (by
      intro a b h
      exact Quotient.sound (T.nested _ μ.succ (Nat.succ_le_succ (Nat.zero_le μ.val)) a b h)))
    (by
      intro a b
      exact Quotient.inductionOn₂ a b (fun _ _ h => Quotient.sound h))
  invFun := fun q => Quotient.liftOn q (fun e => Quotient.mk _ (T.firstWagon e))
    (fun _ _ h => Quotient.sound h)
  left_inv := by
    intro q
    exact Quotient.inductionOn q (fun p => Quotient.inductionOn p (fun _ => rfl))
  right_inv := by
    intro q
    exact Quotient.inductionOn q (fun _ => rfl)

/-- The labelled quotient identification preserves the full old vertex
carrier, with no extra private points yet inserted. -/
theorem contractFirstWagonEquiv_carrier (edge : E → Set V) (μ : Fin (m + 1))
    (a : Quotient (T.contractFirst.wagonSetoid μ)) :
    T.contractFirst.wagonClassCarrier
        (T.wagonClassCarrier edge (0 : Fin (m + 1)).succ) μ a =
      T.wagonClassCarrier edge μ.succ (T.contractFirstWagonEquiv μ a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction a using Quotient.inductionOn with
    | h a =>
      ext x
      constructor
      · rintro ⟨b, hab, hx⟩
        induction b using Quotient.inductionOn with
        | h b =>
          obtain ⟨e, hbe, he⟩ := hx
          exact ⟨e, (T.equivalent μ.succ).trans hab
            (T.nested _ μ.succ (Nat.succ_le_succ (Nat.zero_le μ.val)) b e hbe), he⟩
      · rintro ⟨e, hae, he⟩
        exact ⟨T.firstWagon e, hae, ⟨e, (T.equivalent _).refl e, he⟩⟩

end StructuralRamsey.Girth.EdgeTrainLevels
