import Girth.TrainFillingIndexedHigherCutPrivateGirth
import Girth.TrainFillingIndexedContractedTrain
import Girth.TrainFillingIndexedPrivateParentParameters

set_option Elab.async false

/-!
# Exact proper-cut labelled girth of the actual contracted G0 train

At a proper cut mu<m, the verified contracted train has the quotient
of (choice, old first-wagon) edge labels under its actual equivalence.
It is not enough to identify its classes informally with choice x old
quotient; labelled girth must retain the literal wagon class labels
AND their COMPLETE physical vertex carriers.

Construct the exact quotient equivalence and prove carrier equality
under it. The newly proved expanded/private and dependent tagged
girth transfers then give the quantitative labelled cut bound for
the actual contractedChoiceTrain of the heterogeneous G0.

No new cut-girth premise on the expanded geometry is made. The only
input is the genuine original old wagon cut girth of each choice.
The universal top is excluded. This proves the horizontal cut girth
transfer, not yet adjacent parameters or A2/A3 system girth.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- At every proper cut, actual quotient classes of the contracted
component train are exactly choice-tagged original quotient wagons. -/
noncomputable def contractedWagonClassEquiv
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (μ : Fin (m + 1)) (hProper : μ.val < m) :
    Quotient ((contractedChoiceTrain U T hm).wagonSetoid μ) ≃
      C × Quotient (T.wagonSetoid μ) where
  toFun := fun q => Quotient.liftOn q
    (contractedProperParent U T μ)
    (by
      intro a b hab
      exact (contractedProperParent_eq_iff_rel
        U T hm μ hProper a b).mpr hab)
  invFun := fun cq => Quotient.liftOn cq.2
    (fun p : P => Quotient.mk
      ((contractedChoiceTrain U T hm).wagonSetoid μ) (cq.1, p))
    (by
      intro a b hab
      exact Quotient.sound (Or.inr ⟨rfl, hab⟩))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h e =>
        rcases e with ⟨c, p⟩
        rfl
  right_inv := by
    rintro ⟨c, q⟩
    induction q using Quotient.inductionOn with
    | h p =>
        rfl

/-- The actual quotient wagon in the contracted M has LITERALLY
the complete choice-tagged union of all its full private X-wagons.
This is equality of carrier sets indexed by the true quotient labels,
not just equality of their cardinalities. -/
theorem contractedWagonClass_carrier_eq_tagged
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (μ : Fin (m + 1)) (hProper : μ.val < m)
    (q : Quotient ((contractedChoiceTrain U T hm).wagonSetoid μ)) :
    (contractedChoiceTrain U T hm).wagonClassCarrier
        (contractedCarrier U) μ q =
      dependentTaggedCarriers
        (fun c => T.wagonClassCarrier
          (fun p => Set.range ((U c).place p)) μ)
        (contractedWagonClassEquiv U T hm μ hProper q) := by
  induction q using Quotient.inductionOn with
  | h e =>
      rcases e with ⟨c, p⟩
      ext z
      change
        (∃ f : C × P,
          (μ.val = m ∨ (c = f.1 ∧ T.rel μ p f.2)) ∧
          z ∈ contractedCarrier U f) ↔
        z ∈ (tagVertex U c) ''
          T.wagonCarrier (fun r => Set.range ((U c).place r)) μ p
      constructor
      · rintro ⟨⟨d, r⟩, hRel, hz⟩
        rcases hRel with hTop | ⟨hcd, hpr⟩
        · exact False.elim ((Nat.ne_of_lt hProper) hTop)
        · subst d
          obtain ⟨x, hx, hzEq⟩ := hz
          exact ⟨x, ⟨r, hpr, hx⟩, hzEq⟩
      · rintro ⟨x, ⟨r, hpr, hx⟩, hzEq⟩
        exact ⟨(c, r), Or.inr ⟨rfl, hpr⟩,
          ⟨x, hx, hzEq⟩⟩

/-- The ACTUAL labelled mu-cut of the contracted G0 train has girth
greater than g, solely from the original old cut girth per choice.
No girth of the expanded private structure is assumed separately. -/
theorem contractedChoiceTrain_labelledCutGirth
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (μ : Fin (m + 1)) (hProper : μ.val < m)
    (g : ℕ)
    (hOld : ∀ c : C,
      LabelledGirthGT
        (T.wagonClassCarrier (U c).oldCarrier μ) g) :
    LabelledGirthGT
      ((contractedChoiceTrain U T hm).wagonClassCarrier
        (contractedCarrier U) μ) g := by
  let fam :=
    dependentTaggedCarriers
      (fun c => T.wagonClassCarrier
        (fun p => Set.range ((U c).place p)) μ)
  have hTagged : LabelledGirthGT fam g :=
    indexedExpandedProperCut_labelledGirthGT U T μ g hOld
  have hReindex : LabelledGirthGT
      (fun q => fam (contractedWagonClassEquiv U T hm μ hProper q)) g :=
    labelledGirthGT_of_injective_reindex fam
      (contractedWagonClassEquiv U T hm μ hProper)
      (contractedWagonClassEquiv U T hm μ hProper).injective
      g hTagged
  have hEq :
      (contractedChoiceTrain U T hm).wagonClassCarrier
        (contractedCarrier U) μ =
      (fun q => fam (contractedWagonClassEquiv U T hm μ hProper q)) := by
    funext q
    exact contractedWagonClass_carrier_eq_tagged U T hm μ hProper q
  rw [hEq]
  exact hReindex

/-- The real contracted-train parent square commutes EXACTLY with
choice-tagged original quotient parents at two proper cuts.
This is stronger than preserving the equivalence relations at each
individual cut, because adjacent-parameter bounds depend on parents. -/
theorem contractedWagonClass_parent_eq
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hμ : μ.val < m) (hν : ν.val < m)
    (q : Quotient ((contractedChoiceTrain U T hm).wagonSetoid μ)) :
    contractedWagonClassEquiv U T hm ν hν
      ((contractedChoiceTrain U T hm).wagonParent μ ν hμν q) =
    ((contractedWagonClassEquiv U T hm μ hμ q).1,
      T.wagonParent μ ν hμν
        (contractedWagonClassEquiv U T hm μ hμ q).2) := by
  induction q using Quotient.inductionOn with
  | h e =>
      rcases e with ⟨c, p⟩
      rfl

/-- The ACTUAL contracted train inherits every original sibling
intersection bound between proper cuts. Distinct child μ-wagons
with the same ν-parent can only meet on original old vertices;
private vertices are invisible in sibling intersections.

The permitted output vertices here are precisely the old tagged
vertices whose original V-coordinate is allowed. Any larger union
of allowed predicate parts automatically inherits this bound.
No new parameter bound or output system-girth is assumed. -/
theorem contractedChoiceTrain_parentBound
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hμ : μ.val < m) (hν : ν.val < m)
    (allowed : Set V)
    (hOld : ∀ c : C, TrainParentIntersectionBound
      (T.wagonClassCarrier (U c).oldCarrier μ)
      (T.wagonParent μ ν hμν) allowed) :
    TrainParentIntersectionBound
      ((contractedChoiceTrain U T hm).wagonClassCarrier
        (contractedCarrier U) μ)
      ((contractedChoiceTrain U T hm).wagonParent μ ν hμν)
      {z : Vertex U |
        z.2 ∈ ((Sum.inl : V → (U z.1).Vertex) '' allowed)} := by
  let local : ∀ c : C,
      Quotient (T.wagonSetoid μ) → Set ((U c).Vertex) :=
    fun c => T.wagonClassCarrier
      (fun p => Set.range ((U c).place p)) μ
  let allowedLocal : ∀ c : C, Set ((U c).Vertex) :=
    fun c => ((Sum.inl : V → (U c).Vertex) '' allowed)
  have hLocal : ∀ c : C, TrainParentIntersectionBound
      (local c) (T.wagonParent μ ν hμν) (allowedLocal c) := by
    intro c
    exact PrivateWagonInput.expandedWagonClass_parentBound
      (U c) T μ ν hμν allowed (hOld c)
  have hTagged : TrainParentIntersectionBound
      (dependentTaggedCarriers local)
      (fun cq : C × Quotient (T.wagonSetoid μ) =>
        (cq.1, T.wagonParent μ ν hμν cq.2))
      {z : Vertex U | z.2 ∈ allowedLocal z.1} :=
    trainParentBound_dependentTagged local
      (T.wagonParent μ ν hμν) allowedLocal hLocal
  let fμ := contractedWagonClassEquiv U T hm μ hμ
  let fν := contractedWagonClassEquiv U T hm ν hν
  intro q r hqr hParent z hz
  have hDistinct : fμ q ≠ fμ r := by
    intro heq
    exact hqr (fμ.injective heq)
  have hParTagged :
      ((fμ q).1, T.wagonParent μ ν hμν (fμ q).2) =
      ((fμ r).1, T.wagonParent μ ν hμν (fμ r).2) := by
    calc
      _ = fν
          ((contractedChoiceTrain U T hm).wagonParent μ ν hμν q) :=
        (contractedWagonClass_parent_eq U T hm
          μ ν hμν hμ hν q).symm
      _ = fν
          ((contractedChoiceTrain U T hm).wagonParent μ ν hμν r) :=
        congrArg fν hParent
      _ = _ :=
        contractedWagonClass_parent_eq U T hm μ ν hμν hμ hν r
  have hq : z ∈ dependentTaggedCarriers local (fμ q) := by
    rw [← contractedWagonClass_carrier_eq_tagged
      U T hm μ hμ q]
    exact hz.1
  have hr : z ∈ dependentTaggedCarriers local (fμ r) := by
    rw [← contractedWagonClass_carrier_eq_tagged
      U T hm μ hμ r]
    exact hz.2
  exact hTagged hDistinct hParTagged ⟨hq, hr⟩


end StructuralRamsey.Girth.IndexedPrivateChoice
