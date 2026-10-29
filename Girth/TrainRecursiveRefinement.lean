import Girth.TrainAllAdjacentParameterPreservation
import Girth.LabelledWagonCutRestriction

/-!
# Concrete first-cut refinements of a matching train

Insert finitely many equality levels below the first positive level of an
existing train.  The construction retains every physical edge and agrees
with every old level after the explicit index shift; it does not choose a
new edge subfamily.  For a matching, distinct wagon classes have disjoint
carriers at every cut, so all labelled girth bounds and all allowed-part
sibling bounds hold, including bounds by singleton parts.

These are initial-refinement constructors.  Preservation of a refinement
under a nontrivial attachment, and the girth gain after forgetting it, are
separate statements.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P : Type v}

namespace EdgeTrainLevels

/-- The old level represented by a new level after inserting `d` equality
levels immediately above the original bottom equality. -/
def firstRefinementCollapse (m d : ℕ) (μ : Fin (m + d + 1)) : Fin (m + 1) :=
  ⟨μ.val - d, by have := μ.isLt; omega⟩

/-- The old level `μ` occurs exactly at level `μ + d` in the refinement. -/
def firstRefinementShift (m d : ℕ) (μ : Fin (m + 1)) : Fin (m + d + 1) :=
  ⟨μ.val + d, by have := μ.isLt; omega⟩

/-- Actual nested partitions obtained by inserting equality levels. -/
def insertFirstCuts {m : ℕ} (T : EdgeTrainLevels E m) (d : ℕ) :
    EdgeTrainLevels E (m + d) where
  rel μ := T.rel (firstRefinementCollapse m d μ)
  equivalent μ := T.equivalent _
  nested := by
    intro μ ν hμν e f hef
    apply T.nested _ _ ?_ e f hef
    change μ.val - d ≤ ν.val - d
    exact Nat.sub_le_sub_right hμν d
  bottom := by
    intro e f
    simpa only [firstRefinementCollapse, Nat.zero_sub] using T.bottom e f
  top := by
    intro e f
    have htop : firstRefinementCollapse m d
        ⟨m + d, Nat.lt_succ_self (m + d)⟩ =
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
      apply Fin.ext
      simp [firstRefinementCollapse]
    change T.rel _ e f
    rw [htop]
    exact T.top e f

/-- Every original train relation is preserved and reflected, including the
original bottom and universal top. -/
theorem insertFirstCuts_originalLevel {m : ℕ}
    (T : EdgeTrainLevels E m) (d : ℕ) (μ : Fin (m + 1)) (e f : E) :
    (T.insertFirstCuts d).rel (firstRefinementShift m d μ) e f ↔
      T.rel μ e f := by
  have hμ : firstRefinementCollapse m d (firstRefinementShift m d μ) = μ := by
    apply Fin.ext
    simp [firstRefinementCollapse, firstRefinementShift]
  change T.rel _ e f ↔ _
  rw [hμ]

/-- The inserted lower levels are actual equality partitions. -/
theorem insertFirstCuts_lowerLevel {m : ℕ}
    (T : EdgeTrainLevels E m) (d : ℕ)
    (μ : Fin (m + d + 1)) (hμ : μ.val ≤ d) (e f : E) :
    (T.insertFirstCuts d).rel μ e f ↔ e = f := by
  have hzero : firstRefinementCollapse m d μ =
      (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) := by
    apply Fin.ext
    exact Nat.sub_eq_zero_of_le hμ
  change T.rel _ e f ↔ _
  rw [hzero]
  exact T.bottom e f

/-- Disjoint physical edges give disjoint carriers of distinct wagon
classes, even when the train partitions group many edges together. -/
theorem wagonClassCarrier_disjoint_of_matching {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W)
    (hMatching : ∀ ⦃e f : E⦄, e ≠ f → Disjoint (edge e) (edge f))
    (μ : Fin (m + 1))
    (a b : Quotient (T.wagonSetoid μ)) (hne : a ≠ b) :
    Disjoint (T.wagonClassCarrier edge μ a)
      (T.wagonClassCarrier edge μ b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      rw [Set.disjoint_left]
      rintro x ⟨e, hae, hxe⟩ ⟨f, hbf, hxf⟩
      have hef : e ≠ f := by
        intro hef
        subst f
        apply hne
        exact Quotient.sound ((T.equivalent μ).trans hae
          ((T.equivalent μ).symm hbf))
      exact Set.disjoint_left.mp (hMatching hef) hxe hxf

/-- Matching trains satisfy every sibling-intersection parameter.  In
particular a singleton part may be chosen independently at each inserted
level, with no extra intersection assumption. -/
theorem adjacentParameters_of_matching {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W)
    (hMatching : ∀ ⦃e f : E⦄, e ≠ f → Disjoint (edge e) (edge f))
    (allowed : Fin (m + 1) → Set W) :
    T.AdjacentParameters edge allowed := by
  intro μ ν hμν hsucc a b hne hparent x hx
  exact (Set.disjoint_left.mp
    (T.wagonClassCarrier_disjoint_of_matching edge hMatching μ a b hne)
    hx.1 hx.2).elim

end EdgeTrainLevels

/-- A labelled matching contains no labelled Berge cycle of any length.
The labels are retained; this does not collapse repeated carriers. -/
theorem labelledGirthGT_of_matching
    {J : Type v} (edge : J → Set W)
    (hMatching : ∀ ⦃e f : J⦄, e ≠ f → Disjoint (edge e) (edge f))
    (q : ℕ) : LabelledGirthGT edge q := by
  rintro ⟨c, hq⟩
  let i : Fin c.length := ⟨0, by have := c.hlength; omega⟩
  have hi : i ≠ cyclicSucc i := by
    intro h
    have hv := congrArg Fin.val h
    have hn := c.hlength
    change 0 = (0 + 1) % c.length at hv
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < c.length)] at hv
    exact Nat.zero_ne_one hv
  have hlabel : c.label i ≠ c.label (cyclicSucc i) :=
    fun h => hi (c.label_injective h)
  exact Set.disjoint_left.mp (hMatching hlabel) (c.left_mem i) (c.right_mem i)

/-- Every labelled horizontal wagon cut of a matching has arbitrary girth. -/
theorem EdgeTrainLevels.labelledCutGirth_of_matching {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W)
    (hMatching : ∀ ⦃e f : E⦄, e ≠ f → Disjoint (edge e) (edge f))
    (μ : Fin (m + 1)) (q : ℕ) :
    LabelledGirthGT (T.wagonClassCarrier edge μ) q := by
  exact labelledGirthGT_of_matching _
    (fun {_ _} hne => T.wagonClassCarrier_disjoint_of_matching edge hMatching μ _ _ hne)
    q

/-- The child cut of one inserted refinement step. -/
def firstRefinementChild (m d : ℕ) (hm : 0 < m) (j : Fin (d + 1)) :
    Fin (m + d + 1) := ⟨j.val, by have := j.isLt; omega⟩

/-- The parent cut of one inserted refinement step.  Its last value is the
shifted original first cut. -/
def firstRefinementParent (m d : ℕ) (hm : 0 < m) (j : Fin (d + 1)) :
    Fin (m + d + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩

/-- Exact first-wagon refinement data.  The actual refinement depth is
`extraCuts + 1`, hence is positive.  Singleton bounds mean cardinality at
most one, so an empty permitted-part set is allowed.  Girth is measured on
the labelled family of **all** children of each parent, without identifying
equal carriers or deleting children.  Higher original levels are retained.
-/
structure FirstWagonRefinement {m : ℕ}
    (T : EdgeTrainLevels E m) (hm : 0 < m)
    (edge : E → Set W) (part : W → P) (firstAllowed : Set P) (q : ℕ) where
  extraCuts : ℕ
  train : EdgeTrainLevels E (m + extraCuts)
  oldLevels : ∀ (μ : Fin (m + 1)), 0 < μ.val → ∀ e f : E,
    train.rel (EdgeTrainLevels.firstRefinementShift m extraCuts μ) e f ↔
      T.rel μ e f
  permitted : Fin (extraCuts + 1) → Set P
  permitted_subset : ∀ j, permitted j ⊆ firstAllowed
  permitted_subsingleton : ∀ j, (permitted j).Subsingleton
  parameters : ∀ j : Fin (extraCuts + 1),
    TrainParentIntersectionBound
      (train.wagonClassCarrier edge (firstRefinementChild m extraCuts hm j))
      (train.wagonParent (firstRefinementChild m extraCuts hm j)
        (firstRefinementParent m extraCuts hm j) (by
          change j.val ≤ j.val + 1; omega))
      (part ⁻¹' permitted j)
  childGirth : ∀ (j : Fin (extraCuts + 1))
    (p : Quotient (train.wagonSetoid (firstRefinementParent m extraCuts hm j))),
    LabelledGirthGT
      (fun a : {a : Quotient
          (train.wagonSetoid (firstRefinementChild m extraCuts hm j)) //
        train.wagonParent (firstRefinementChild m extraCuts hm j)
          (firstRefinementParent m extraCuts hm j)
          (by change j.val ≤ j.val + 1; omega) a = p} =>
        train.wagonClassCarrier edge (firstRefinementChild m extraCuts hm j) a.val)
      q

/-- Construct a first-wagon refinement of any prescribed finite depth from
a matching.  All inserted permitted-part sets are empty; their subset and
singleton-size conditions therefore require no extra hypotheses.
-/
def firstWagonRefinement_of_matching {m : ℕ}
    (T : EdgeTrainLevels E m) (hm : 0 < m)
    (edge : E → Set W)
    (hMatching : ∀ ⦃e f : E⦄, e ≠ f → Disjoint (edge e) (edge f))
    (part : W → P) (firstAllowed : Set P) (q d : ℕ) :
    FirstWagonRefinement T hm edge part firstAllowed q where
  extraCuts := d
  train := T.insertFirstCuts d
  oldLevels μ _ e f := T.insertFirstCuts_originalLevel d μ e f
  permitted := fun _ => ∅
  permitted_subset := fun _ => Set.empty_subset _
  permitted_subsingleton := fun _ => Set.subsingleton_empty
  parameters := by
    intro j a b hne hparent x hx
    exact (Set.disjoint_left.mp
      ((T.insertFirstCuts d).wagonClassCarrier_disjoint_of_matching
        edge hMatching (firstRefinementChild m d hm j) a b hne) hx.1 hx.2).elim
  childGirth := by
    intro j p
    exact labelledGirthGT_of_injective_reindex
      ((T.insertFirstCuts d).wagonClassCarrier edge (firstRefinementChild m d hm j))
      Subtype.val Subtype.val_injective q
      ((T.insertFirstCuts d).labelledCutGirth_of_matching edge hMatching _ q)

end StructuralRamsey.Girth
