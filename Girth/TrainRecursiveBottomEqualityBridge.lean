import Girth.TrainRecursiveMixedBottomRefinement
import Girth.TrainBottomOrdinaryLabelledGirth

set_option autoImplicit false

/-!
# The bottom physical equality cut and its genuine wagon quotient

A train's bottom relation is equality of physical edge labels.  Therefore
its quotient wagon labels are canonically the original physical edges,
with exactly the same carriers.  This is an actual labelled equivalence,
not a replacement of a labelled hypergraph by its unlabelled carrier set.

The resulting bridge feeds the ordinary bottom A-support forest girth
directly into the verified first-refinement constructor: only strictly
positive inserted coordinates need full system-girth certificates.
The actual recursive local witness and its positive-cut bounds are
still separate obligations.
-/

namespace StructuralRamsey.Girth

universe u v
variable {E W : Type v}

namespace EdgeTrainLevels

/-- At bottom equality, a wagon class determines its unique physical edge. -/
def bottomQuotientEdge {m : ℕ} (T : EdgeTrainLevels E m) :
    Quotient (T.wagonSetoid (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))) → E :=
  fun p => Quotient.liftOn p (fun e : E => e) (by
    intro a b hab
    exact (T.bottom a b).mp hab)

@[simp] theorem bottomQuotientEdge_mk {m : ℕ}
    (T : EdgeTrainLevels E m) (e : E) :
    T.bottomQuotientEdge
      (Quotient.mk (T.wagonSetoid (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))) e) =
        e := rfl

/-- Distinct bottom wagon labels determine distinct physical edge labels. -/
theorem bottomQuotientEdge_injective {m : ℕ} (T : EdgeTrainLevels E m) :
    Function.Injective T.bottomQuotientEdge := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change a = b at hab
      subst b
      rfl

/-- The full carrier of a bottom wagon is literally its one physical edge. -/
theorem bottom_wagonClassCarrier_mk {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W) (e : E) :
    T.wagonClassCarrier edge (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
      (Quotient.mk (T.wagonSetoid (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))) e) =
        edge e := by
  ext x
  change (∃ b : E,
      T.rel (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) e b ∧ x ∈ edge b) ↔
    x ∈ edge e
  constructor
  · rintro ⟨b, hab, hx⟩
    have heq : e = b := (T.bottom e b).mp hab
    subst b
    exact hx
  · intro hx
    exact ⟨e, (T.bottom e e).mpr rfl, hx⟩

/-- Exact equality of the quotient-labelled bottom family and the original
physical edge family after the injective canonical relabelling. -/
theorem bottom_wagonClassCarrier_eq {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W) :
    T.wagonClassCarrier edge (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) =
      fun p => edge (T.bottomQuotientEdge p) := by
  funext p
  induction p using Quotient.inductionOn with
  | h e =>
    exact T.bottom_wagonClassCarrier_mk edge e

/-- Labelled girth of the actual physical edges implies labelled girth
of the ENTIRE bottom wagon quotient family, with no discarded labels. -/
theorem bottom_labelledCutGirth_of_edgeGirth {m : ℕ}
    (T : EdgeTrainLevels E m) (edge : E → Set W) (g : ℕ)
    (hEdge : LabelledGirthGT edge g) :
    LabelledGirthGT
      (T.wagonClassCarrier edge (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))) g := by
  rw [T.bottom_wagonClassCarrier_eq edge]
  exact labelledGirthGT_of_injective_reindex
    edge T.bottomQuotientEdge T.bottomQuotientEdge_injective g hEdge

end EdgeTrainLevels

section PhysicalRefinement

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- Construct a genuine first-wagon refinement using ONLY ordinary girth of
the whole physical A-support at the bottom cut and full system girth at
strictly positive inserted child cuts.  The actual fine train and its
parent-intersection parameters remain explicit geometric inputs. -/
def FirstWagonRefinement.ofFineTrain_of_ordinaryBottomAndPositiveSystemBounds
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m)
    (part : X → P) (firstAllowed : Set P) (g : ℕ)
    (permitted : Fin (d + 1) → Set P)
    (hSubset : ∀ j, permitted j ⊆ firstAllowed)
    (hSingleton : ∀ j, (permitted j).Subsingleton)
    (hParameters : ∀ j : Fin (d + 1),
      TrainParentIntersectionBound
        (T.wagonClassCarrier (fun edge => edge.1)
          (firstRefinementChild m d hm j))
        (T.wagonParent (firstRefinementChild m d hm j)
          (firstRefinementParent m d hm j)
          (by change j.val ≤ j.val + 1; omega))
        (part ⁻¹' permitted j))
    (hBottomOrdinary : GirthGT (supportCopies A C.toRelStructure) g)
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) part firstAllowed g := by
  have hEdge :
      LabelledGirthGT
        (fun e : OldACarrierEdge A C.toRelStructure => e.1) g :=
    physicalASupport_labelledGirth_of_girth A C.toRelStructure g hBottomOrdinary
  have hBottom :
      LabelledGirthGT
        (T.wagonClassCarrier (fun edge => edge.1)
          (firstRefinementChild m d hm
            (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))) g := by
    change LabelledGirthGT
      (T.wagonClassCarrier (fun edge => edge.1)
        (⟨0, Nat.zero_lt_succ (m + d)⟩ : Fin (m + d + 1))) g
    exact T.bottom_labelledCutGirth_of_edgeGirth (fun edge => edge.1) g hEdge
  exact FirstWagonRefinement.ofFineTrain_of_bottomAndPositiveSystemBounds
    A B D C family selected T hm part firstAllowed g
    permitted hSubset hSingleton hParameters hBottom hFullPositive

end PhysicalRefinement

end StructuralRamsey.Girth
