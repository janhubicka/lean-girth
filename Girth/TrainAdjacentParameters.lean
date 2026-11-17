import Girth.TrainParameterRestriction
import Girth.TrainSharedEdgeQuotients

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

universe v

variable {E V : Type v}

/-- Distinct children of a wagon can intersect only at vertices allowed
by the parameter of their parent cut. -/
def EdgeTrainLevels.AdjacentParameters
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edgeCarrier : E → Set V)
    (allowed : Fin (m + 1) → Set V) : Prop :=
  ∀ (μ ν : Fin (m + 1)) (hμν : μ ≤ ν),
    ν.val = μ.val + 1 →
      TrainParentIntersectionBound
        (T.wagonClassCarrier edgeCarrier μ)
        (T.wagonParent μ ν hμν)
        (allowed ν)

/-- The height-one train has equality at the bottom and one universal
top wagon. It has no interior cut to fill. -/
def EdgeTrainLevels.heightOne (E : Type v) : EdgeTrainLevels E 1 where
  rel μ e f := μ.val = 0 → e = f
  equivalent μ := ⟨fun _ _ => rfl, fun h hp => (h hp).symm,
    fun h₁ h₂ hp => (h₁ hp).trans (h₂ hp)⟩
  nested μ ν hLe _ _ hRel hZero := by
    apply hRel
    have hLe' : μ.val ≤ ν.val := hLe
    omega
  bottom _ _ := ⟨fun h => h rfl, fun h _ => h⟩
  top _ _ h := (Nat.one_ne_zero h).elim

/-- At height one the adjacent parameter is exactly the allowed-contact
condition on distinct physical edges. Every such pair has the same
parent, and the bottom wagon contains just its own edge. -/
theorem EdgeTrainLevels.adjacentParameters_heightOne_iff
    (T : EdgeTrainLevels E 1) (edge : E → Set V) (allowed : Fin 2 → Set V) :
    T.AdjacentParameters edge allowed ↔
      ∀ a b : E, a ≠ b → edge a ∩ edge b ⊆ allowed 1 := by
  have hCarrier (a : E) :
      T.wagonClassCarrier edge 0 (Quotient.mk (T.wagonSetoid 0) a) = edge a := by
    ext x
    change (∃ b : E, T.rel 0 a b ∧ x ∈ edge b) ↔ x ∈ edge a
    constructor
    · rintro ⟨b, hab, hx⟩
      have hEq : a = b := (T.bottom a b).mp hab
      simpa only [hEq] using hx
    · intro hx
      exact ⟨a, (T.bottom a a).mpr rfl, hx⟩
  constructor
  · intro h a b hNe x hx
    have hBottom :
        Quotient.mk (T.wagonSetoid 0) a ≠ Quotient.mk (T.wagonSetoid 0) b := by
      intro hEq
      exact hNe ((T.bottom a b).mp (Quotient.exact hEq))
    have hParent :
        T.wagonParent 0 1 (by decide) (Quotient.mk (T.wagonSetoid 0) a) =
          T.wagonParent 0 1 (by decide) (Quotient.mk (T.wagonSetoid 0) b) :=
      Quotient.sound (T.top a b)
    apply h 0 1 (by decide) (by decide) hBottom hParent
    simpa only [hCarrier] using hx
  · intro h μ ν hLe hNext
    have hLt : ν.val < 2 := ν.isLt
    have hZeroVal : μ.val = 0 := by omega
    have hOneVal : ν.val = 1 := by omega
    have hZero : μ = 0 := Fin.ext hZeroVal
    have hOne : ν = 1 := Fin.ext hOneVal
    subst μ
    subst ν
    intro c d hNe _ x hx
    induction c using Quotient.inductionOn with
    | _ a =>
      induction d using Quotient.inductionOn with
      | _ b =>
        have hDistinct : a ≠ b := fun hEq =>
          hNe (congrArg (Quotient.mk (T.wagonSetoid 0)) hEq)
        apply h a b hDistinct
        simpa only [hCarrier] using hx

end StructuralRamsey.Girth
