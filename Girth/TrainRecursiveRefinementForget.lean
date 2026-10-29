import Girth.TrainRecursiveRefinement

/-!
# Forgetting the extra first refinement cuts

For a fine train of height `m + d`, retain level zero at zero and each
positive old level `μ` at `μ + d`.  The special treatment of zero is
necessary: the refined level `d` need not be equality.  No physical edge
is removed, and retained wagon labels, carriers, and parent maps agree.

The fine train's actual singleton-part parameters and complete labelled
child-girth bounds reconstruct a `FirstWagonRefinement` of the coarse train.
Conversely, forgetting the fine train in an existing refinement recovers
the original train.  This is a construction on supplied train data; it does
not derive child girth from system girth or preserve a refinement through
an attachment.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P : Type v}

namespace EdgeTrainLevels

/-- The retained fine level: zero stays zero, while every positive level
skips the `d` extra first cuts. -/
def firstForgetIndex (m d : ℕ) (μ : Fin (m + 1)) : Fin (m + d + 1) :=
  ⟨if μ.val = 0 then 0 else μ.val + d, by
    split_ifs <;> have := μ.isLt <;> omega⟩

@[simp] theorem firstForgetIndex_zero (m d : ℕ) :
    firstForgetIndex m d ⟨0, Nat.zero_lt_succ m⟩ =
      ⟨0, Nat.zero_lt_succ (m + d)⟩ := by
  apply Fin.ext
  simp [firstForgetIndex]

/-- The positive retained levels are precisely the existing refinement
shift.  The bottom level is deliberately excluded from this identity. -/
theorem firstForgetIndex_of_pos (m d : ℕ) (μ : Fin (m + 1)) (hμ : 0 < μ.val) :
    firstForgetIndex m d μ = firstRefinementShift m d μ := by
  apply Fin.ext
  simp [firstForgetIndex, firstRefinementShift, Nat.ne_of_gt hμ]

theorem firstForgetIndex_monotone (m d : ℕ) : Monotone (firstForgetIndex m d) := by
  intro μ ν hμν
  change (if μ.val = 0 then 0 else μ.val + d) ≤
    (if ν.val = 0 then 0 else ν.val + d)
  have hval : μ.val ≤ ν.val := hμν
  split_ifs <;> omega

/-- Coarsen an actual fine train, retaining every physical edge and every
positive original level with its exact shift. -/
def forgetFirstCuts {m d : ℕ} (T : EdgeTrainLevels E (m + d)) (hm : 0 < m) :
    EdgeTrainLevels E m where
  rel μ := T.rel (firstForgetIndex m d μ)
  equivalent μ := T.equivalent _
  nested μ ν hμν e f hef :=
    T.nested _ _ (firstForgetIndex_monotone m d hμν) e f hef
  bottom := by
    intro e f
    simpa only [firstForgetIndex_zero] using T.bottom e f
  top := by
    intro e f
    have htop : firstForgetIndex m d ⟨m, Nat.lt_succ_self m⟩ =
        (⟨m + d, Nat.lt_succ_self (m + d)⟩ : Fin (m + d + 1)) := by
      apply Fin.ext
      simp [firstForgetIndex, Nat.ne_of_gt hm]
    change T.rel _ e f
    rw [htop]
    exact T.top e f

theorem forgetFirstCuts_rel_iff {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (μ : Fin (m + 1)) (e f : E) :
    (T.forgetFirstCuts hm).rel μ e f ↔ T.rel (firstForgetIndex m d μ) e f := Iff.rfl

/-- Every positive retained relation is both preserved and reflected. -/
theorem forgetFirstCuts_rel_iff_of_pos {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (μ : Fin (m + 1)) (hμ : 0 < μ.val) (e f : E) :
    (T.forgetFirstCuts hm).rel μ e f ↔ T.rel (firstRefinementShift m d μ) e f := by
  rw [T.forgetFirstCuts_rel_iff hm, firstForgetIndex_of_pos m d μ hμ]

/-- Retaining a level keeps exactly the same quotient labels, including
distinct labels whose carriers happen to coincide. -/
def forgetFirstCuts_wagonEquiv {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m) (μ : Fin (m + 1)) :
    Quotient ((T.forgetFirstCuts hm).wagonSetoid μ) ≃
      Quotient (T.wagonSetoid (firstForgetIndex m d μ)) := Equiv.refl _

@[simp] theorem forgetFirstCuts_wagonEquiv_mk {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m) (μ : Fin (m + 1)) (e : E) :
    T.forgetFirstCuts_wagonEquiv hm μ (Quotient.mk _ e) = Quotient.mk _ e := rfl

theorem forgetFirstCuts_wagonCarrier {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W) (μ : Fin (m + 1)) (e : E) :
    (T.forgetFirstCuts hm).wagonCarrier edge μ e =
      T.wagonCarrier edge (firstForgetIndex m d μ) e := rfl

/-- Complete retained wagon carriers are unchanged under the exact
quotient equivalence; no carrier-shrinking or support deletion occurs. -/
theorem forgetFirstCuts_wagonClassCarrier {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W) (μ : Fin (m + 1))
    (p : Quotient ((T.forgetFirstCuts hm).wagonSetoid μ)) :
    (T.forgetFirstCuts hm).wagonClassCarrier edge μ p =
      T.wagonClassCarrier edge (firstForgetIndex m d μ)
        (T.forgetFirstCuts_wagonEquiv hm μ p) := rfl

/-- Parent maps between retained levels commute with their label
equivalences.  Both endpoints use the actual retained fine levels. -/
theorem forgetFirstCuts_wagonParent {m d : ℕ}
    (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (p : Quotient ((T.forgetFirstCuts hm).wagonSetoid μ)) :
    T.forgetFirstCuts_wagonEquiv hm ν
        ((T.forgetFirstCuts hm).wagonParent μ ν hμν p) =
      T.wagonParent (firstForgetIndex m d μ) (firstForgetIndex m d ν)
        (firstForgetIndex_monotone m d hμν)
        (T.forgetFirstCuts_wagonEquiv hm μ p) := by
  induction p using Quotient.inductionOn with
  | h e => rfl

end EdgeTrainLevels

namespace FirstWagonRefinement

/-- Reconstruct the exact refinement record of a forgotten fine train from
its supplied singleton-part parameters and all-child labelled girth bounds.
The coarse train is constructed here; no ordinary output girth is assumed.
-/
def ofFineTrain {m d : ℕ} (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W) (part : W → P) (firstAllowed : Set P) (g : ℕ)
    (permitted : Fin (d + 1) → Set P)
    (hSubset : ∀ j, permitted j ⊆ firstAllowed)
    (hSingleton : ∀ j, (permitted j).Subsingleton)
    (hParameters : ∀ j : Fin (d + 1),
      TrainParentIntersectionBound
        (T.wagonClassCarrier edge (firstRefinementChild m d hm j))
        (T.wagonParent (firstRefinementChild m d hm j)
          (firstRefinementParent m d hm j) (by change j.val ≤ j.val + 1; omega))
        (part ⁻¹' permitted j))
    (hChildGirth : ∀ (j : Fin (d + 1))
      (p : Quotient (T.wagonSetoid (firstRefinementParent m d hm j))),
      LabelledGirthGT
        (fun a : {a : Quotient (T.wagonSetoid (firstRefinementChild m d hm j)) //
          T.wagonParent (firstRefinementChild m d hm j)
            (firstRefinementParent m d hm j)
            (by change j.val ≤ j.val + 1; omega) a = p} =>
          T.wagonClassCarrier edge (firstRefinementChild m d hm j) a.val) g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm edge part firstAllowed g where
  extraCuts := d
  train := T
  oldLevels μ hμ e f := (T.forgetFirstCuts_rel_iff_of_pos hm μ hμ e f).symm
  permitted := permitted
  permitted_subset := hSubset
  permitted_subsingleton := hSingleton
  parameters := hParameters
  childGirth := hChildGirth

/-- Forgetting an existing refinement recovers every original relation.
The bottom case uses equality directly, and positive cuts use oldLevels. -/
theorem forget_rel_iff {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P} {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (μ : Fin (m + 1)) (e f : E) :
    (R.train.forgetFirstCuts hm).rel μ e f ↔ T.rel μ e f := by
  by_cases hμ : μ.val = 0
  · have hzero : μ = (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) := Fin.ext hμ
    subst μ
    exact (R.train.forgetFirstCuts hm).bottom e f |>.trans (T.bottom e f).symm
  · have hpos : 0 < μ.val := Nat.pos_of_ne_zero hμ
    exact (R.train.forgetFirstCuts_rel_iff_of_pos hm μ hpos e f).trans
      (R.oldLevels μ hpos e f)

/-- The entire original train, not merely its set of carriers, is recovered
by forgetting the extra cuts of its refinement. -/
theorem forget_train_eq {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P} {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm edge part firstAllowed g) :
    R.train.forgetFirstCuts hm = T := by
  have ext : ∀ S U : EdgeTrainLevels E m, S.rel = U.rel → S = U := by
    rintro ⟨s, _, _, _, _⟩ ⟨u, _, _, _, _⟩ h
    cases h
    rfl
  apply ext
  funext μ e f
  exact propext (R.forget_rel_iff μ e f)

end FirstWagonRefinement
end StructuralRamsey.Girth
