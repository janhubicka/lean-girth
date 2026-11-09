import Girth.TrainRecursiveBottomEqualityBridge
import Girth.TrainRecursiveRefinementStepGirth

set_option autoImplicit false

/-!
# First children are acyclic from a singleton parameter

The first child family consists of physical edges. Transversality and a
singleton permitted part already rule out every labelled cycle in one parent.
Thus rebuilding a first-wagon refinement requires system bounds only at the
positive inserted cuts; no bottom forest or ordinary bottom girth is used here.
The outer forest increment still needs its separate mixed-forest hypothesis.
-/

namespace StructuralRamsey.Girth

universe u v
variable {E V P J : Type v}

/-- A transversal labelled family whose pairwise overlaps lie in one part
has arbitrary labelled girth. Labels are never identified by carrier equality. -/
theorem labelledGirthGT_of_singleton_intersections
    (edge : E → Set V) (part : V → P) (allowed : Set P)
    (hAllowed : allowed.Subsingleton)
    (hPart : ∀ e, Set.InjOn part (edge e))
    (hInter : ∀ e f, e ≠ f → edge e ∩ edge f ⊆ part ⁻¹' allowed)
    (g : ℕ) : LabelledGirthGT edge g := by
  rintro ⟨C, _⟩
  exact C.child_not_injective_of_singleton_intersections
    C.label edge part allowed hAllowed (fun i => hPart (C.label i))
    (fun _ => Set.Subset.rfl) hInter C.label_injective

/-- The same fact for all children of a fixed parent, retaining every label. -/
theorem labelledFibreGirthGT_of_singleton_intersections
    (edge : E → Set V) (parent : E → J) (part : V → P) (allowed : Set P)
    (hAllowed : allowed.Subsingleton)
    (hPart : ∀ e, Set.InjOn part (edge e))
    (hParameter : TrainParentIntersectionBound edge parent (part ⁻¹' allowed))
    (p : J) (g : ℕ) :
    LabelledGirthGT (fun e : {e // parent e = p} => edge e.val) g := by
  apply labelledGirthGT_of_singleton_intersections
    (fun e : {e // parent e = p} => edge e.val) part allowed hAllowed
    (fun e => hPart e.val) ?_ g
  intro e f hne x hx
  exact hParameter (fun h => hne (Subtype.ext h))
    (e.property.trans f.property.symm) hx

namespace FirstWagonRefinement

/-- Rebuild the refinement from singleton parameters and positive child
bounds. Acyclicity of the zero child family is derived from transversality. -/
def ofFineTrain_of_singletonAndPositiveChildBounds
    {m d : ℕ} (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set V) (part : V → P) (firstAllowed : Set P) (g : ℕ)
    (hPart : ∀ e, Set.InjOn part (edge e))
    (permitted : Fin (d + 1) → Set P)
    (hSubset : ∀ j, permitted j ⊆ firstAllowed)
    (hSingleton : ∀ j, (permitted j).Subsingleton)
    (hParameters : ∀ j : Fin (d + 1),
      TrainParentIntersectionBound
        (T.wagonClassCarrier edge (firstRefinementChild m d hm j))
        (T.wagonParent (firstRefinementChild m d hm j)
          (firstRefinementParent m d hm j)
          (by change j.val ≤ j.val + 1; omega)) (part ⁻¹' permitted j))
    (hPositive : ∀ (j : Fin (d + 1)), 0 < j.val →
      ∀ p : Quotient (T.wagonSetoid (firstRefinementParent m d hm j)),
      LabelledGirthGT
        (fun a : {a : Quotient (T.wagonSetoid (firstRefinementChild m d hm j)) //
          T.wagonParent (firstRefinementChild m d hm j)
            (firstRefinementParent m d hm j)
            (by change j.val ≤ j.val + 1; omega) a = p} =>
          T.wagonClassCarrier edge (firstRefinementChild m d hm j) a.val) g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm edge part firstAllowed g := by
  apply FirstWagonRefinement.ofFineTrain T hm edge part firstAllowed g
    permitted hSubset hSingleton hParameters
  intro j p
  by_cases hz : j.val = 0
  · have hj : j = (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)) := Fin.ext hz
    subst j
    apply labelledFibreGirthGT_of_singleton_intersections _ _ part _
      (hSingleton _) _ (hParameters _)
    intro a
    induction a using Quotient.inductionOn with
    | h e =>
      change Set.InjOn part (T.wagonClassCarrier edge
        (⟨0, Nat.zero_lt_succ (m + d)⟩ : Fin (m + d + 1)) (Quotient.mk _ e))
      rw [T.bottom_wagonClassCarrier_mk]
      exact hPart e
  · exact hPositive j (Nat.pos_of_ne_zero hz) p

/-- The actual selected physical train needs full system bounds only at
strictly positive inserted cuts for this refinement reconstruction. -/
def ofFineTrain_of_singletonAndPositiveSystemBounds
    {L : RelLanguage.{u}} {UA VB X : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m) (part : X → P) (firstAllowed : Set P) (g : ℕ)
    (hPart : ∀ e : OldACarrierEdge A C.toRelStructure, Set.InjOn part e.val)
    (permitted : Fin (d + 1) → Set P)
    (hSubset : ∀ j, permitted j ⊆ firstAllowed)
    (hSingleton : ∀ j, (permitted j).Subsingleton)
    (hParameters : ∀ j : Fin (d + 1),
      TrainParentIntersectionBound
        (T.wagonClassCarrier (fun edge => edge.val) (firstRefinementChild m d hm j))
        (T.wagonParent (firstRefinementChild m d hm j)
          (firstRefinementParent m d hm j)
          (by change j.val ≤ j.val + 1; omega)) (part ⁻¹' permitted j))
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.val) part firstAllowed g := by
  apply ofFineTrain_of_singletonAndPositiveChildBounds T hm
    (fun edge => edge.val) part firstAllowed g hPart
    permitted hSubset hSingleton hParameters
  intro j hj p
  exact selectedPicture_childGirth_of_fullSystemGirth A B D C family selected T
    (firstRefinementChild m d hm j) (firstRefinementParent m d hm j)
    (by change j.val ≤ j.val + 1; omega) p g (hFullPositive j hj)

end FirstWagonRefinement
end StructuralRamsey.Girth
