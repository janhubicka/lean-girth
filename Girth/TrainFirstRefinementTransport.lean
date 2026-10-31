import Girth.TrainRecursiveRefinement
import Girth.TrainWagonQuotientTransport

set_option Elab.async false
set_option autoImplicit false

/-!
# First-wagon refinements across a physical edge equivalence

The complete refinement, including its labelled child families and actual
parent maps, transports along a carrier-preserving bijection of physical
edges.  Equal vertex carriers do not identify distinct wagon labels.
This allows a refinement constructed on standard/old-edge pairs to be
returned to the full actual untouched support.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W P : Type v}

/-- The bottom-to-first wagon parameter applies to two distinct physical
edges of one first wagon.  This is the permitted-part input for the new
refinement level, derived from the existing output train parameters. -/
theorem EdgeTrainLevels.firstEdgeIntersection_of_adjacent
    {m : ℕ} (T : EdgeTrainLevels E m) (hm : 0 < m)
    (edge : E → Set W) (allowed : Fin (m + 1) → Set W)
    (hParameters : T.AdjacentParameters edge allowed)
    (a b : E) (hne : a ≠ b)
    (hFirst : T.rel ⟨1, Nat.succ_lt_succ hm⟩ a b) :
    edge a ∩ edge b ⊆ allowed ⟨1, Nat.succ_lt_succ hm⟩ := by
  let zero : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
  let one : Fin (m + 1) := ⟨1, Nat.succ_lt_succ hm⟩
  have hle : zero ≤ one := by change 0 ≤ 1; omega
  have hClasses : Quotient.mk (T.wagonSetoid zero) a ≠
      Quotient.mk (T.wagonSetoid zero) b := by
    intro h
    exact hne ((T.bottom a b).mp (Quotient.exact h))
  have hParent : T.wagonParent zero one hle (Quotient.mk _ a) =
      T.wagonParent zero one hle (Quotient.mk _ b) := by
    exact Quotient.sound hFirst
  intro x hx
  exact hParameters zero one hle rfl hClasses hParent
    ⟨⟨a, (T.equivalent zero).refl a, hx.1⟩,
      ⟨b, (T.equivalent zero).refl b, hx.2⟩⟩

/-- The complete child family of every parent retains its labelled girth
under a carrier-preserving physical edge equivalence. -/
theorem EdgeTrainLevels.wagonTransport_childGirth
    {m : ℕ} (T : EdgeTrainLevels E m) (ϕ : E ≃ F)
    (oldCarrier : E → Set W) (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) (g : ℕ)
    (hOld : ∀ p : Quotient (T.wagonSetoid ν),
      LabelledGirthGT
        (fun a : {a : Quotient (T.wagonSetoid μ) //
          T.wagonParent μ ν hμν a = p} =>
          T.wagonClassCarrier oldCarrier μ a.val) g) :
    ∀ p : Quotient ((T.transport ϕ).wagonSetoid ν),
      LabelledGirthGT
        (fun a : {a : Quotient ((T.transport ϕ).wagonSetoid μ) //
          (T.transport ϕ).wagonParent μ ν hμν a = p} =>
          (T.transport ϕ).wagonClassCarrier newCarrier μ a.val) g := by
  intro p
  let parent := (T.wagonTransportEquiv ϕ ν).symm p
  let child :
      {a : Quotient ((T.transport ϕ).wagonSetoid μ) //
        (T.transport ϕ).wagonParent μ ν hμν a = p} →
      {a : Quotient (T.wagonSetoid μ) // T.wagonParent μ ν hμν a = parent} :=
    fun a => ⟨(T.wagonTransportEquiv ϕ μ).symm a.val, by
      change T.wagonParent μ ν hμν ((T.wagonTransportEquiv ϕ μ).symm a.val) =
        (T.wagonTransportEquiv ϕ ν).symm p
      rw [T.wagonTransport_parent_symm ϕ μ ν hμν a.val, a.property]⟩
  have hChild : Function.Injective child := by
    intro a b hab
    apply Subtype.ext
    apply (T.wagonTransportEquiv ϕ μ).symm.injective
    exact congrArg Subtype.val hab
  apply labelledGirthGT_of_injective_shrinking
    (fun a : {a : Quotient (T.wagonSetoid μ) //
      T.wagonParent μ ν hμν a = parent} => T.wagonClassCarrier oldCarrier μ a.val)
    _ child hChild _ g (hOld parent)
  intro a
  have hc := T.wagonTransport_carrier_eq ϕ oldCarrier newCarrier hCarrier μ
    ((T.wagonTransportEquiv ϕ μ).symm a.val)
  rw [Equiv.apply_symm_apply] at hc
  change (T.transport ϕ).wagonClassCarrier newCarrier μ a.val ⊆
    T.wagonClassCarrier oldCarrier μ ((T.wagonTransportEquiv ϕ μ).symm a.val)
  exact hc.subset

/-- Return a complete refinement to any exactly equivalent physical train.
The target train is supplied only as the edge-reindexed original train;
all refinement partitions, parent fibres, parameters and girth fields
are transported from the constructed source refinement. -/
noncomputable def FirstWagonRefinement.transport
    {m : ℕ} {T : EdgeTrainLevels E m} (hm : 0 < m)
    {oldCarrier : E → Set W} {part : W → P}
    {firstAllowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm oldCarrier part firstAllowed g)
    (ϕ : E ≃ F) (U : EdgeTrainLevels F m)
    (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (hTrain : ∀ (μ : Fin (m + 1)) (e f : E),
      U.rel μ (ϕ e) (ϕ f) ↔ T.rel μ e f) :
    FirstWagonRefinement U hm newCarrier part firstAllowed g where
  extraCuts := R.extraCuts
  train := R.train.transport ϕ
  oldLevels := by
    intro μ hμ e f
    change R.train.rel (EdgeTrainLevels.firstRefinementShift m R.extraCuts μ)
      (ϕ.symm e) (ϕ.symm f) ↔ U.rel μ e f
    have hU := hTrain μ (ϕ.symm e) (ϕ.symm f)
    simp only [ϕ.apply_symm_apply] at hU
    exact (R.oldLevels μ hμ (ϕ.symm e) (ϕ.symm f)).trans hU.symm
  permitted := R.permitted
  permitted_subset := R.permitted_subset
  permitted_subsingleton := R.permitted_subsingleton
  parameters := by
    intro j
    exact R.train.wagonTransport_parentIntersectionBound ϕ oldCarrier newCarrier hCarrier
      (firstRefinementChild m R.extraCuts hm j)
      (firstRefinementParent m R.extraCuts hm j)
      (by change j.val ≤ j.val + 1; omega)
      (part ⁻¹' R.permitted j) (R.parameters j)
  childGirth := by
    intro j
    exact R.train.wagonTransport_childGirth ϕ oldCarrier newCarrier hCarrier
      (firstRefinementChild m R.extraCuts hm j)
      (firstRefinementParent m R.extraCuts hm j)
      (by change j.val ≤ j.val + 1; omega) g (R.childGirth j)

end StructuralRamsey.Girth
