import Girth.TrainFirstRefinementAppendTrain
import Girth.TrainRecursiveInitialTailIncidence

set_option Elab.async false
set_option autoImplicit false

/-!
# The complete appended first-wagon refinement

Copy an old refinement inside every standard and append the actual output
first relation.  The lower quotient labels and their parent maps are kept
exactly.  Injective vertex images transport every inherited parameter and
labelled child-girth bound.  At the new level, the owner map is injective
only within the complete child fibre of one actual first parent.

The fresh permitted set is the intersection of the output first allowed
set and a common subsingleton part set.  Its first clause follows from two
literal incident physical edges in the same output first class.  Its second
clause follows from cross-standard localization.  A general local bound
for injectively owned subcarrier families supplies the new labelled girth;
the actual child family and its owner injection are constructed here.
-/

namespace StructuralRamsey.Girth.FirstRefinementAppend

universe v
variable {I X Y P Q R Q' R' : Type v}

/-- Exact product labels, parent compatibility, and full injective carrier
images transport an inherited sibling-intersection bound. -/
theorem product_parentIntersectionBound
    (oldCarrier : Q → Set X) (newCarrier : Q' → Set Y)
    (oldParent : Q → R) (newParent : Q' → R')
    (child : Q' ≃ I × Q) (parent : R' ≃ I × R)
    (std : I → X → Y) (hStd : ∀ i, Function.Injective (std i))
    (hCarrier : ∀ a, newCarrier a = std (child a).1 '' oldCarrier (child a).2)
    (hParent : ∀ a, parent (newParent a) = ((child a).1, oldParent (child a).2))
    (oldPart : X → P) (newPart : Y → P)
    (hPart : ∀ i x, newPart (std i x) = oldPart x)
    (allowed : Set P)
    (hOld : TrainParentIntersectionBound oldCarrier oldParent (oldPart ⁻¹' allowed)) :
    TrainParentIntersectionBound newCarrier newParent (newPart ⁻¹' allowed) := by
  intro a b hne hparent y hy
  have hLabels : ((child a).1, oldParent (child a).2) =
      ((child b).1, oldParent (child b).2) :=
    (hParent a).symm.trans ((congrArg parent hparent).trans (hParent b))
  have hOwner : (child a).1 = (child b).1 :=
    congrArg (fun z : I × R => z.1) hLabels
  have hOldParent : oldParent (child a).2 = oldParent (child b).2 :=
    congrArg (fun z : I × R => z.2) hLabels
  have hOldNe : (child a).2 ≠ (child b).2 := by
    intro h
    exact hne (child.injective (Prod.ext hOwner h))
  rw [hCarrier a, hCarrier b] at hy
  rcases hy.1 with ⟨x, hx, rfl⟩
  rcases hy.2 with ⟨z, hz, hzx⟩
  rw [← hOwner] at hzx
  have hzEq : z = x := hStd _ hzx
  subst z
  change newPart (std (child a).1 x) ∈ allowed
  rw [hPart]
  exact hOld hOldNe hOldParent ⟨hx, hz⟩

/-- The full new child fibre injects into the old child fibre of its fixed
standard owner.  Labelled girth transports through the exact carrier image. -/
theorem product_childGirth
    (oldCarrier : Q → Set X) (newCarrier : Q' → Set Y)
    (oldParent : Q → R) (newParent : Q' → R')
    (child : Q' ≃ I × Q) (parent : R' ≃ I × R)
    (std : I → X → Y) (hStd : ∀ i, Function.Injective (std i))
    (hCarrier : ∀ a, newCarrier a = std (child a).1 '' oldCarrier (child a).2)
    (hParent : ∀ a, parent (newParent a) = ((child a).1, oldParent (child a).2))
    (g : ℕ)
    (hOld : ∀ p : R,
      LabelledGirthGT (fun a : {a : Q // oldParent a = p} => oldCarrier a.val) g) :
    ∀ p : R',
      LabelledGirthGT (fun a : {a : Q' // newParent a = p} => newCarrier a.val) g := by
  intro p
  have hOwner (a : {a : Q' // newParent a = p}) :
      (child a.val).1 = (parent p).1 := by
    exact congrArg (fun z : I × R => z.1)
      ((hParent a.val).symm.trans (congrArg parent a.property))
  let label : {a : Q' // newParent a = p} →
      {a : Q // oldParent a = (parent p).2} := fun a =>
    ⟨(child a.val).2, congrArg (fun z : I × R => z.2)
      ((hParent a.val).symm.trans (congrArg parent a.property))⟩
  have hLabel : Function.Injective label := by
    intro a b hab
    apply Subtype.ext
    apply child.injective
    exact Prod.ext ((hOwner a).trans (hOwner b).symm) (congrArg Subtype.val hab)
  have hImage := labelledGirthGT_image
    (fun a : {a : Q // oldParent a = (parent p).2} => oldCarrier a.val)
    (std (parent p).1) (hStd _) g (hOld (parent p).2)
  refine labelledGirthGT_of_injective_shrinking _ _ label hLabel ?_ g hImage
  intro a
  change newCarrier a.val ⊆ std (parent p).1 '' oldCarrier (label a).val
  rw [hCarrier a.val, hOwner a]
  exact Set.Subset.rfl

private theorem classCarrier_has_edge
    {F Z : Type v} {n : ℕ} (V : EdgeTrainLevels F n)
    (edge : F → Set Z) (μ : Fin (n + 1))
    (a : Quotient (V.wagonSetoid μ)) {x : Z}
    (hx : x ∈ V.wagonClassCarrier edge μ a) :
    ∃ e : F, Quotient.mk (V.wagonSetoid μ) e = a ∧ x ∈ edge e := by
  induction a using Quotient.inductionOn with
  | h a =>
      obtain ⟨e, hae, hxe⟩ := hx
      exact ⟨e, Quotient.sound ((V.equivalent μ).symm hae), hxe⟩

section Fresh

variable {E : Type v} {m d : ℕ}
variable (hm : 0 < m) (V : EdgeTrainLevels E (m + d))
variable (U : EdgeTrainLevels (I × E) m)
variable (hFirst : ∀ (i : I) (a b : E),
  V.rel (oldLowIndex m d hm (Fin.last (d + 1))) a b ↔
    U.rel ⟨1, by omega⟩ (i, a) (i, b))
variable (edge : E → Set X) (std : I → X → Y)

/-- Every actual new child is contained in the complete edge support of
its derived standard owner. -/
theorem freshChildCarrier_subset_standard
    (p : Quotient ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm)))
    (a : {a : Quotient ((train hm V U hFirst).wagonSetoid
        (lowIndex m d hm (Fin.last (d + 1)))) //
      (train hm V U hFirst).wagonParent
        (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
        (by change d + 1 ≤ d + 2; omega) a = p}) :
    (train hm V U hFirst).wagonClassCarrier
        (fun ie => std ie.1 '' edge ie.2)
        (lowIndex m d hm (Fin.last (d + 1))) a.val ⊆
      {y | ∃ e, y ∈ std (freshChildOwner hm V U hFirst p a) '' edge e} := by
  rw [lowerWagon_carrier hm V U hFirst edge std]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨e, _, hxe⟩ := classCarrier_has_edge V edge
    (oldLowIndex m d hm (Fin.last (d + 1)))
    (lowerWagonEquiv hm V U hFirst (Fin.last (d + 1)) a.val).2 hx
  exact ⟨e, x, hxe, rfl⟩

/-- The appended sibling bound uses both the output first parameter and
cross-standard localization.  The witnesses are actual physical edges. -/
theorem fresh_parentIntersectionBound
    (newPart : Y → P) (firstAllowed common : Set P)
    (hCross : ∀ ⦃i j : I⦄, i ≠ j → ∀ ⦃a b : E⦄ ⦃y : Y⦄,
      y ∈ std i '' edge a → y ∈ std j '' edge b → newPart y ∈ common)
    (hParameter : ∀ ⦃a b : I × E⦄, a ≠ b → U.rel ⟨1, by omega⟩ a b →
      (std a.1 '' edge a.2) ∩ (std b.1 '' edge b.2) ⊆ newPart ⁻¹' firstAllowed) :
    TrainParentIntersectionBound
      ((train hm V U hFirst).wagonClassCarrier
        (fun ie => std ie.1 '' edge ie.2) (lowIndex m d hm (Fin.last (d + 1))))
      ((train hm V U hFirst).wagonParent
        (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
        (by change d + 1 ≤ d + 2; omega))
      (newPart ⁻¹' (firstAllowed ∩ common)) := by
  intro a b hne hparent y hy
  let p := (train hm V U hFirst).wagonParent
    (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
    (by change d + 1 ≤ d + 2; omega) a
  let aa : {c : Quotient ((train hm V U hFirst).wagonSetoid
      (lowIndex m d hm (Fin.last (d + 1)))) //
    (train hm V U hFirst).wagonParent
      (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
      (by change d + 1 ≤ d + 2; omega) c = p} := ⟨a, rfl⟩
  let bb : {c : Quotient ((train hm V U hFirst).wagonSetoid
      (lowIndex m d hm (Fin.last (d + 1)))) //
    (train hm V U hFirst).wagonParent
      (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
      (by change d + 1 ≤ d + 2; omega) c = p} := ⟨b, hparent.symm⟩
  have hOwners : freshChildOwner hm V U hFirst p aa ≠
      freshChildOwner hm V U hFirst p bb := by
    intro h
    exact hne (congrArg Subtype.val (freshChildOwner_injective hm V U hFirst p h))
  have hCommon : newPart y ∈ common := by
    obtain ⟨e, he⟩ := freshChildCarrier_subset_standard hm V U hFirst edge std p aa hy.1
    obtain ⟨f, hf⟩ := freshChildCarrier_subset_standard hm V U hFirst edge std p bb hy.2
    exact hCross hOwners he hf
  obtain ⟨e, he, hye⟩ := classCarrier_has_edge (train hm V U hFirst)
    (fun ie => std ie.1 '' edge ie.2) (lowIndex m d hm (Fin.last (d + 1))) a hy.1
  obtain ⟨f, hf, hyf⟩ := classCarrier_has_edge (train hm V U hFirst)
    (fun ie => std ie.1 '' edge ie.2) (lowIndex m d hm (Fin.last (d + 1))) b hy.2
  have hef : e ≠ f := by
    intro h
    exact hne (he.symm.trans ((congrArg (Quotient.mk _) h).trans hf))
  have hParents : Quotient.mk
      ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm)) e =
      Quotient.mk _ f := by
    exact (congrArg ((train hm V U hFirst).wagonParent
      (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
      (by change d + 1 ≤ d + 2; omega)) he).trans
      (hparent.trans (congrArg ((train hm V U hFirst).wagonParent
        (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
        (by change d + 1 ≤ d + 2; omega)) hf).symm)
  have hOutput : U.rel ⟨1, by omega⟩ e f :=
    (freshParent_rel hm V U hFirst e f).mp (Quotient.exact hParents)
  exact ⟨hParameter hef hOutput ⟨hye, hyf⟩, hCommon⟩

/-- Apply the independent local subcarrier bound to the entire actual
child family, using its derived containment and parent-local owner injection. -/
theorem fresh_childGirth (g : ℕ)
    (hFresh : ∀ (J : Type v) (carrier : J → Set Y) (owner : J → I),
      Function.Injective owner →
      (∀ a, carrier a ⊆ {y | ∃ e, y ∈ std (owner a) '' edge e}) →
      LabelledGirthGT carrier g) :
    ∀ p : Quotient ((train hm V U hFirst).wagonSetoid (freshParentIndex m d hm)),
      LabelledGirthGT
        (fun a : {a : Quotient ((train hm V U hFirst).wagonSetoid
            (lowIndex m d hm (Fin.last (d + 1)))) //
          (train hm V U hFirst).wagonParent
            (lowIndex m d hm (Fin.last (d + 1))) (freshParentIndex m d hm)
            (by change d + 1 ≤ d + 2; omega) a = p} =>
          (train hm V U hFirst).wagonClassCarrier
            (fun ie => std ie.1 '' edge ie.2)
            (lowIndex m d hm (Fin.last (d + 1))) a.val) g := by
  intro p
  exact hFresh _ _ (freshChildOwner hm V U hFirst p)
    (freshChildOwner_injective hm V U hFirst p)
    (freshChildCarrier_subset_standard hm V U hFirst edge std p)

end Fresh

/-- Increase the refinement depth by one, preserving all actual physical
edges, every positive output cut, and all labelled child-girth fields. -/
noncomputable def append
    {E : Type v} {m : ℕ}
    (T : EdgeTrainLevels E m) (hm : 0 < m)
    (edge : E → Set X) (oldPart : X → P) (firstAllowed : Set P) (g : ℕ)
    (R : FirstWagonRefinement T hm edge oldPart firstAllowed g)
    (U : EdgeTrainLevels (I × E) m)
    (hStandard : ∀ (i : I) (a b : E),
      U.rel ⟨1, by omega⟩ (i, a) (i, b) ↔ T.rel ⟨1, by omega⟩ a b)
    (std : I → X → Y) (hStd : ∀ i, Function.Injective (std i))
    (newPart : Y → P) (hPart : ∀ i x, newPart (std i x) = oldPart x)
    (common : Set P) (hCommon : common.Subsingleton)
    (hCross : ∀ ⦃i j : I⦄, i ≠ j → ∀ ⦃a b : E⦄ ⦃y : Y⦄,
      y ∈ std i '' edge a → y ∈ std j '' edge b → newPart y ∈ common)
    (hParameter : ∀ ⦃a b : I × E⦄, a ≠ b → U.rel ⟨1, by omega⟩ a b →
      (std a.1 '' edge a.2) ∩ (std b.1 '' edge b.2) ⊆ newPart ⁻¹' firstAllowed)
    (hFresh : ∀ (J : Type v) (carrier : J → Set Y) (owner : J → I),
      Function.Injective owner →
      (∀ a, carrier a ⊆ {y | ∃ e, y ∈ std (owner a) '' edge e}) →
      LabelledGirthGT carrier g) :
    FirstWagonRefinement U hm (fun ie => std ie.1 '' edge ie.2)
      newPart firstAllowed g := by
  classical
  have hFirst : ∀ (i : I) (a b : E),
      R.train.rel (oldLowIndex m R.extraCuts hm (Fin.last (R.extraCuts + 1))) a b ↔
        U.rel ⟨1, by omega⟩ (i, a) (i, b) := by
    intro i a b
    have hIndex : oldLowIndex m R.extraCuts hm (Fin.last (R.extraCuts + 1)) =
        EdgeTrainLevels.firstRefinementShift m R.extraCuts ⟨1, by omega⟩ := by
      apply Fin.ext
      change R.extraCuts + 1 = 1 + R.extraCuts
      omega
    rw [hIndex]
    exact (R.oldLevels ⟨1, by omega⟩ (by change (0 : ℕ) < 1; omega) a b).trans
      (hStandard i a b).symm
  refine {
    extraCuts := R.extraCuts + 1
    train := train hm R.train U hFirst
    oldLevels := oldLevels hm R.train U hFirst
    permitted := fun j => if h : j.val < R.extraCuts + 1 then
      R.permitted ⟨j.val, h⟩ else firstAllowed ∩ common
    permitted_subset := ?_
    permitted_subsingleton := ?_
    parameters := ?_
    childGirth := ?_
  }
  · intro j
    by_cases hj : j.val < R.extraCuts + 1
    · simp only [dite_eq_left hj]
      exact R.permitted_subset ⟨j.val, hj⟩
    · simp only [dite_eq_right hj]
      exact fun _ hx => hx.1
  · intro j
    by_cases hj : j.val < R.extraCuts + 1
    · simp only [dite_eq_left hj]
      exact R.permitted_subsingleton ⟨j.val, hj⟩
    · simp only [dite_eq_right hj]
      intro x hx y hy
      exact hCommon hx.2 hy.2
  · intro j
    by_cases hj : j.val < R.extraCuts + 1
    · simp only [dite_eq_left hj]
      let oldj : Fin (R.extraCuts + 1) := ⟨j.val, hj⟩
      let μ : Fin (R.extraCuts + 2) := oldj.castSucc
      let ν : Fin (R.extraCuts + 2) := oldj.succ
      have hμν : μ ≤ ν := by change oldj.val ≤ oldj.val + 1; omega
      have hOld : TrainParentIntersectionBound
          (R.train.wagonClassCarrier edge (oldLowIndex m R.extraCuts hm μ))
          (R.train.wagonParent (oldLowIndex m R.extraCuts hm μ)
            (oldLowIndex m R.extraCuts hm ν) hμν)
          (oldPart ⁻¹' R.permitted oldj) := by
        simpa only [oldLowIndex, firstRefinementChild, firstRefinementParent, μ, ν]
          using R.parameters oldj
      have hBound := product_parentIntersectionBound
        (R.train.wagonClassCarrier edge (oldLowIndex m R.extraCuts hm μ))
        ((train hm R.train U hFirst).wagonClassCarrier
          (fun ie => std ie.1 '' edge ie.2) (lowIndex m R.extraCuts hm μ))
        (R.train.wagonParent (oldLowIndex m R.extraCuts hm μ)
          (oldLowIndex m R.extraCuts hm ν) hμν)
        ((train hm R.train U hFirst).wagonParent (lowIndex m R.extraCuts hm μ)
          (lowIndex m R.extraCuts hm ν) hμν)
        (lowerWagonEquiv hm R.train U hFirst μ)
        (lowerWagonEquiv hm R.train U hFirst ν) std hStd
        (lowerWagon_carrier hm R.train U hFirst edge std μ)
        (lowerWagon_parent hm R.train U hFirst μ ν hμν)
        oldPart newPart hPart (R.permitted oldj) hOld
      simpa only [lowIndex, firstRefinementChild, firstRefinementParent, μ, ν, oldj]
        using hBound
    · have hjLast : j = Fin.last (R.extraCuts + 1) := by
        apply Fin.ext
        change j.val = R.extraCuts + 1
        have := j.isLt
        omega
      subst j
      simp only [Fin.val_last, dite_eq_right (Nat.lt_irrefl _)]
      simpa only [lowIndex, freshParentIndex, firstRefinementChild, firstRefinementParent]
        using fresh_parentIntersectionBound hm R.train U hFirst edge std
          newPart firstAllowed common hCross hParameter
  · intro j
    by_cases hj : j.val < R.extraCuts + 1
    · let oldj : Fin (R.extraCuts + 1) := ⟨j.val, hj⟩
      let μ : Fin (R.extraCuts + 2) := oldj.castSucc
      let ν : Fin (R.extraCuts + 2) := oldj.succ
      have hμν : μ ≤ ν := by change oldj.val ≤ oldj.val + 1; omega
      have hOld : ∀ p : Quotient (R.train.wagonSetoid (oldLowIndex m R.extraCuts hm ν)),
          LabelledGirthGT
            (fun a : {a : Quotient (R.train.wagonSetoid (oldLowIndex m R.extraCuts hm μ)) //
              R.train.wagonParent (oldLowIndex m R.extraCuts hm μ)
                (oldLowIndex m R.extraCuts hm ν) hμν a = p} =>
              R.train.wagonClassCarrier edge (oldLowIndex m R.extraCuts hm μ) a.val) g := by
        simpa only [oldLowIndex, firstRefinementChild, firstRefinementParent, μ, ν]
          using R.childGirth oldj
      have hGirth := product_childGirth
        (R.train.wagonClassCarrier edge (oldLowIndex m R.extraCuts hm μ))
        ((train hm R.train U hFirst).wagonClassCarrier
          (fun ie => std ie.1 '' edge ie.2) (lowIndex m R.extraCuts hm μ))
        (R.train.wagonParent (oldLowIndex m R.extraCuts hm μ)
          (oldLowIndex m R.extraCuts hm ν) hμν)
        ((train hm R.train U hFirst).wagonParent (lowIndex m R.extraCuts hm μ)
          (lowIndex m R.extraCuts hm ν) hμν)
        (lowerWagonEquiv hm R.train U hFirst μ)
        (lowerWagonEquiv hm R.train U hFirst ν) std hStd
        (lowerWagon_carrier hm R.train U hFirst edge std μ)
        (lowerWagon_parent hm R.train U hFirst μ ν hμν) g hOld
      simpa only [lowIndex, firstRefinementChild, firstRefinementParent, μ, ν, oldj]
        using hGirth
    · have hjLast : j = Fin.last (R.extraCuts + 1) := by
        apply Fin.ext
        change j.val = R.extraCuts + 1
        have := j.isLt
        omega
      subst j
      simpa only [lowIndex, freshParentIndex, firstRefinementChild, firstRefinementParent]
        using fresh_childGirth hm R.train U hFirst edge std g hFresh

end StructuralRamsey.Girth.FirstRefinementAppend
