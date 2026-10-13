import Girth.TrainEdgeEquivalenceTransport
import Girth.TrainSharedEdgeQuotients
import Girth.TrainWagonClassRestriction
import Girth.TrainParameterRestriction

/-!
# Faithful transport of actual wagon classes, parents and part bounds

Transporting a nested train along a genuine physical edge bijection
does not merely preserve equivalence on representatives. At each
horizontal cut it induces a BIJECTION of labelled wagon classes.
Those bijections commute with every parent map. If the edge
bijection preserves each physical edge's vertex carrier, they
preserve the carrier of every wagon class exactly.

Consequently ALL allowed-part sibling-intersection bounds are
invariant under representation change. This is a transport result,
NOT the missing proof that a newly generated picture train obeys
its allowed-part bounds in the first place.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

namespace EdgeTrainLevels

/-- The physical edge bijection induces a bijection between its
actual wagon quotient classes at every horizontal cut. -/
noncomputable def wagonTransportEquiv
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) (μ : Fin (m + 1)) :
    Quotient (T.wagonSetoid μ) ≃
      Quotient ((T.transport ϕ).wagonSetoid μ) where
  toFun := fun q => Quotient.liftOn q
    (fun a : E => Quotient.mk ((T.transport ϕ).wagonSetoid μ) (ϕ a))
    (by
      intro a b hab
      exact Quotient.sound ((T.transport_rel_iff ϕ μ a b).mpr hab))
  invFun := fun q => Quotient.liftOn q
    (fun b : F => Quotient.mk (T.wagonSetoid μ) (ϕ.symm b))
    (by
      intro a b hab
      exact Quotient.sound hab)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
        change Quotient.mk (T.wagonSetoid μ) (ϕ.symm (ϕ a)) =
          Quotient.mk (T.wagonSetoid μ) a
        simp
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
        change Quotient.mk ((T.transport ϕ).wagonSetoid μ)
            (ϕ (ϕ.symm a)) =
          Quotient.mk ((T.transport ϕ).wagonSetoid μ) a
        simp

/-- Parent maps commute EXACTLY with the bijections of genuine
wagon quotient classes. -/
theorem wagonTransport_parent
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) (μ ν : Fin (m + 1))
    (hμν : μ ≤ ν)
    (q : Quotient (T.wagonSetoid μ)) :
    (T.transport ϕ).wagonParent μ ν hμν
        (T.wagonTransportEquiv ϕ μ q) =
      T.wagonTransportEquiv ϕ ν
        (T.wagonParent μ ν hμν q) := by
  induction q using Quotient.inductionOn with
  | h a =>
      rfl

/-- This is the inverse-direction parent square on the actual
transported quotient labels. -/
theorem wagonTransport_parent_symm
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F) (μ ν : Fin (m + 1))
    (hμν : μ ≤ ν)
    (q : Quotient ((T.transport ϕ).wagonSetoid μ)) :
    T.wagonParent μ ν hμν
        ((T.wagonTransportEquiv ϕ μ).symm q) =
      (T.wagonTransportEquiv ϕ ν).symm
        ((T.transport ϕ).wagonParent μ ν hμν q) := by
  induction q using Quotient.inductionOn with
  | h a =>
      rfl

/-- Every labelled wagon quotient class has EXACTLY its original
vertex carrier under a carrier-preserving physical edge bijection. -/
theorem wagonTransport_carrier_eq
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F)
    (oldCarrier : E → Set W)
    (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (μ : Fin (m + 1))
    (q : Quotient (T.wagonSetoid μ)) :
    (T.transport ϕ).wagonClassCarrier newCarrier μ
        (T.wagonTransportEquiv ϕ μ q) =
      T.wagonClassCarrier oldCarrier μ q := by
  induction q using Quotient.inductionOn with
  | h a =>
      change
        (T.transport ϕ).wagonCarrier newCarrier μ (ϕ a) =
          T.wagonCarrier oldCarrier μ a
      exact T.transport_wagonCarrier_eq
        ϕ oldCarrier newCarrier hCarrier μ a

/-- A transport preserving physical edge vertex carriers preserves
the full parent/child allowed-vertex intersection restriction.
All wagon labels remain distinct and both parent squares commute. -/
theorem wagonTransport_parentIntersectionBound
    {m : ℕ} (T : EdgeTrainLevels E m)
    (ϕ : E ≃ F)
    (oldCarrier : E → Set W)
    (newCarrier : F → Set W)
    (hCarrier : ∀ e : E, newCarrier (ϕ e) = oldCarrier e)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (allowed : Set W)
    (hOld : TrainParentIntersectionBound
      (T.wagonClassCarrier oldCarrier μ)
      (T.wagonParent μ ν hμν) allowed) :
    TrainParentIntersectionBound
      ((T.transport ϕ).wagonClassCarrier newCarrier μ)
      ((T.transport ϕ).wagonParent μ ν hμν) allowed := by
  let child :
      Quotient ((T.transport ϕ).wagonSetoid μ) ↪
        Quotient (T.wagonSetoid μ) :=
    (T.wagonTransportEquiv ϕ μ).symm.toEmbedding
  let parent :
      Quotient ((T.transport ϕ).wagonSetoid ν) →
        Quotient (T.wagonSetoid ν) :=
    (T.wagonTransportEquiv ϕ ν).symm
  have hParent : ∀ a,
      T.wagonParent μ ν hμν (child a) =
        parent ((T.transport ϕ).wagonParent μ ν hμν a) := by
    intro a
    exact T.wagonTransport_parent_symm ϕ μ ν hμν a
  have hShrink : ∀ a,
      (T.transport ϕ).wagonClassCarrier newCarrier μ a ⊆
        T.wagonClassCarrier oldCarrier μ (child a) := by
    intro a
    have hc :
        (T.transport ϕ).wagonClassCarrier newCarrier μ a =
          T.wagonClassCarrier oldCarrier μ
            ((T.wagonTransportEquiv ϕ μ).symm a) := by
      let b := (T.wagonTransportEquiv ϕ μ).symm a
      have heq : (T.wagonTransportEquiv ϕ μ) b = a :=
        (T.wagonTransportEquiv ϕ μ).apply_symm_apply a
      rw [← heq]
      simpa only [Equiv.symm_apply_apply] using
        (T.wagonTransport_carrier_eq
          ϕ oldCarrier newCarrier hCarrier μ b)
    change (T.transport ϕ).wagonClassCarrier newCarrier μ a ⊆
      T.wagonClassCarrier oldCarrier μ
        ((T.wagonTransportEquiv ϕ μ).symm a)
    rw [hc]
  exact trainParentIntersectionBound_restrict
    (T.wagonClassCarrier oldCarrier μ)
    (T.wagonParent μ ν hμν)
    ((T.transport ϕ).wagonClassCarrier newCarrier μ)
    ((T.transport ϕ).wagonParent μ ν hμν)
    allowed hOld child parent hParent hShrink

end EdgeTrainLevels
end StructuralRamsey.Girth
