import Girth.ContactTrainData
import Girth.ContactForgetLevels

/-! The actual new level relations for a one-step refinement.
The edge labels of a future strip are (standard, old strip edge).
Through level d retain the old refined equivalences separately in
each standard; from level d+1 onward retain the output train.
The boundary compatibility is exactly reflection of the original
first equivalence in each standard. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I Q : Type v}

/-- Insert the old d levels separately in each standard below the
retained original first level. The new train has d+1 refinement
levels followed by the original tail. -/
structure ContactSplitRefinement (d h : ℕ) where
  depth_pos : 0 < d
  old : ContactTrainData E (d+h)
  coarse : ContactTrainData (Q × E) (h+1)
  boundary : ∀ i e f,
    old.parent ⟨d,by omega⟩ e = old.parent ⟨d,by omega⟩ f ↔
      coarse.parent ⟨1,by omega⟩ (i,e) = coarse.parent ⟨1,by omega⟩ (i,f)

namespace ContactSplitRefinement
variable {d h : ℕ} (R : ContactSplitRefinement (E := E) (Q := Q) d h)

def depthLevel (_R : ContactSplitRefinement (E := E) (Q := Q) d h) (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d) : Fin (d+h+1) :=
  ⟨μ.val,by omega⟩

def tailLevel (_R : ContactSplitRefinement (E := E) (Q := Q) d h) (μ : Fin (d+1+h+1)) (hμ : d < μ.val) : Fin (h+1+1) :=
  ⟨μ.val-d,by have := μ.isLt; omega⟩

def rel (μ : Fin (d+1+h+1)) (e f : Q × E) : Prop :=
  if hμ : μ.val ≤ d then e.1 = f.1 ∧
    R.old.parent (R.depthLevel μ hμ) e.2 = R.old.parent (R.depthLevel μ hμ) f.2
  else R.coarse.parent (R.tailLevel μ (by omega)) e =
    R.coarse.parent (R.tailLevel μ (by omega)) f

theorem rel_prefix (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d) (e f : Q × E) :
    R.rel μ e f ↔ e.1 = f.1 ∧
      R.old.parent (R.depthLevel μ hμ) e.2 =
        R.old.parent (R.depthLevel μ hμ) f.2 := by simp [rel,hμ]

theorem rel_tail (μ : Fin (d+1+h+1)) (hμ : d < μ.val) (e f : Q × E) :
    R.rel μ e f ↔ R.coarse.parent (R.tailLevel μ hμ) e =
      R.coarse.parent (R.tailLevel μ hμ) f := by simp [rel,show ¬ μ.val ≤ d by omega]

theorem rel_equivalence (μ : Fin (d+1+h+1)) : Equivalence (R.rel μ) := by
  classical
  by_cases hμ : μ.val ≤ d
  · refine ⟨fun e => (R.rel_prefix μ hμ e e).mpr ⟨rfl,rfl⟩,?_,?_⟩
    · intro e f hef
      obtain ⟨ha,hb⟩ := (R.rel_prefix μ hμ e f).mp hef
      exact (R.rel_prefix μ hμ f e).mpr ⟨ha.symm,hb.symm⟩
    · intro e f g hef hfg
      obtain ⟨ha,hb⟩ := (R.rel_prefix μ hμ e f).mp hef
      obtain ⟨hc,hd⟩ := (R.rel_prefix μ hμ f g).mp hfg
      exact (R.rel_prefix μ hμ e g).mpr ⟨ha.trans hc,hb.trans hd⟩
  · have hμ' : d < μ.val := by omega
    refine ⟨fun e => (R.rel_tail μ hμ' e e).mpr rfl,?_,?_⟩
    · intro e f hef
      exact (R.rel_tail μ hμ' f e).mpr ((R.rel_tail μ hμ' e f).mp hef).symm
    · intro e f g hef hfg
      exact (R.rel_tail μ hμ' e g).mpr (((R.rel_tail μ hμ' e f).mp hef).trans
        ((R.rel_tail μ hμ' f g).mp hfg))

theorem rel_nested (μ ν : Fin (d+1+h+1)) (hle : μ ≤ ν)
    (e f : Q × E) (hef : R.rel μ e f) : R.rel ν e f := by
  have hval : μ.val ≤ ν.val := hle
  by_cases hν : ν.val ≤ d
  · have hμ : μ.val ≤ d := by omega
    obtain ⟨ha,hb⟩ := (R.rel_prefix μ hμ e f).mp hef
    exact (R.rel_prefix ν hν e f).mpr ⟨ha,R.old.nested _ _ (by exact hval) _ _ hb⟩
  · have hν' : d < ν.val := by omega
    apply (R.rel_tail ν hν' e f).mpr
    by_cases hμ : μ.val ≤ d
    · obtain ⟨ha,hb⟩ := (R.rel_prefix μ hμ e f).mp hef
      have hb' := R.old.nested (R.depthLevel μ hμ) ⟨d,by omega⟩ (by exact hμ) _ _ hb
      rcases e with ⟨i,e⟩
      rcases f with ⟨j,f⟩
      change i = j at ha
      subst j
      have hc := (R.boundary i e f).mp hb'
      exact R.coarse.nested ⟨1,by omega⟩ (R.tailLevel ν hν')
        (by change 1 ≤ ν.val-d; omega) _ _ hc
    · have hμ' : d < μ.val := by omega
      exact R.coarse.nested _ _ (by change μ.val-d ≤ ν.val-d; omega)
        _ _ ((R.rel_tail μ hμ' e f).mp hef)

def levels : EdgeTrainLevels (Q × E) (d+1+h) where
  rel := R.rel
  equivalent := R.rel_equivalence
  nested := R.rel_nested
  bottom := by
    intro e f
    rw [R.rel_prefix _ (by change 0 ≤ d; omega)]
    constructor
    · rintro ⟨ha,hb⟩
      exact Prod.ext ha (R.old.bottom hb)
    · intro he
      subst f
      exact ⟨rfl,rfl⟩
  top := by
    intro e f
    apply (R.rel_tail _ (by change d < d+1+h; omega) e f).mpr
    have he : R.tailLevel ⟨d+1+h,by omega⟩ (by change d < d+1+h; omega) =
        (⟨h+1,by omega⟩ : Fin (h+1+1)) := by
      apply Fin.ext
      change d+1+h-d = h+1
      omega
    rw [he]
    exact R.coarse.top e f

def train : ContactTrainData (Q × E) (d+1+h) := R.levels.toContactTrain

theorem prefix_eq (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d) (e f : Q × E) :
    R.train.parent μ e = R.train.parent μ f ↔ e.1 = f.1 ∧
      R.old.parent (R.depthLevel μ hμ) e.2 =
        R.old.parent (R.depthLevel μ hμ) f.2 := by
  exact (show R.train.parent μ e = R.train.parent μ f ↔ R.rel μ e f from
    ⟨fun he => Quotient.exact he,fun he => Quotient.sound he⟩).trans (R.rel_prefix μ hμ e f)

theorem tail_eq (μ : Fin (d+1+h+1)) (hμ : d < μ.val) (e f : Q × E) :
    R.train.parent μ e = R.train.parent μ f ↔
      R.coarse.parent (R.tailLevel μ hμ) e = R.coarse.parent (R.tailLevel μ hμ) f := by
  exact (show R.train.parent μ e = R.train.parent μ f ↔ R.rel μ e f from
    ⟨fun he => Quotient.exact he,fun he => Quotient.sound he⟩).trans (R.rel_tail μ hμ e f)

/-- The actual labels in a prefix cut are pairs of standard
and old-refinement wagon. They are not just a set of carriers. -/
noncomputable def prefixWagonEquiv (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d) :
    R.train.Wagon μ ≃ Q × R.old.Wagon (R.depthLevel μ hμ) := by
  let g : Q × E → Q × R.old.Wagon (R.depthLevel μ hμ) :=
    fun e => (e.1,R.old.parent (R.depthLevel μ hμ) e.2)
  let f : R.train.Wagon μ → Q × R.old.Wagon (R.depthLevel μ hμ) :=
    Quotient.lift g (fun e f h => Prod.ext ((R.rel_prefix μ hμ e f).mp h).1
      ((R.rel_prefix μ hμ e f).mp h).2)
  have hinj : Function.Injective f := by
    intro a b he
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        change g a = g b at he
        exact Quotient.sound ((R.rel_prefix μ hμ a b).mpr
          ⟨congrArg (fun x : Q × R.old.Wagon (R.depthLevel μ hμ) => x.1) he,
            congrArg (fun x : Q × R.old.Wagon (R.depthLevel μ hμ) => x.2) he⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨i,p⟩
    obtain ⟨e,he⟩ := R.old.surj (R.depthLevel μ hμ) p
    exact ⟨R.train.parent μ (i,e),Prod.ext rfl he⟩
  exact Equiv.ofBijective f ⟨hinj,hsurj⟩

theorem prefixWagonEquiv_parent (μ : Fin (d+1+h+1)) (hμ : μ.val ≤ d) (e : Q × E) :
    R.prefixWagonEquiv μ hμ (R.train.parent μ e) =
      (e.1,R.old.parent (R.depthLevel μ hμ) e.2) := rfl

/-- The retained positive levels have exactly the old coarse
wagon labels, by bijective quotient relabelling. -/
noncomputable def tailWagonEquiv (μ : Fin (d+1+h+1)) (hμ : d < μ.val) :
    R.train.Wagon μ ≃ R.coarse.Wagon (R.tailLevel μ hμ) := by
  let f : R.train.Wagon μ → R.coarse.Wagon (R.tailLevel μ hμ) :=
    Quotient.lift (R.coarse.parent (R.tailLevel μ hμ))
      (fun e f he => (R.rel_tail μ hμ e f).mp he)
  have hi : Function.Injective f := by
    intro a b he
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b => exact Quotient.sound ((R.rel_tail μ hμ a b).mpr he)
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨e,he⟩ := R.coarse.surj (R.tailLevel μ hμ) p
    exact ⟨R.train.parent μ e,he⟩
  exact Equiv.ofBijective f ⟨hi,hs⟩

theorem tailWagonEquiv_parent (μ : Fin (d+1+h+1)) (hμ : d < μ.val) (e : Q × E) :
    R.tailWagonEquiv μ hμ (R.train.parent μ e) =
      R.coarse.parent (R.tailLevel μ hμ) e := rfl

end ContactSplitRefinement
end StructuralRamsey.Girth
