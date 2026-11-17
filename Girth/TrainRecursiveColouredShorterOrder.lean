import Girth.TrainFillingColouredOrderedEdgePresentation
import Girth.TrainLabelledPhysicalToOrdinaryGirth
import Girth.TrainRecursiveProjectedOrderConversion

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
open CoverageFree.Physical

universe v
variable {A X M : Type v} {k : ℕ} {tail : List ℕ}
variable [Finite X] [Nontrivial X]

/-- Apply the all-edge-type order theorem at the shorter vector to the
coloured type enumerated by the filling template. The palette is the
actual finite word of edge colours. -/
theorem shorterOrder_of_colouredTarget
    (ht : Admissible tail)
    (part : X → A) (enumerate : X ≃ ULift.{v} (Fin k))
    (B : RelStructure (colouredOrderedEdgeLanguage A k).withOrder M)
    [Finite M] [LinearOrder M] (hExtends : B.ExtendsOrder)
    (T : EdgeTrainLevels (OldACarrierEdge
      (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered B)
      tail.length)
    (symbols : Fin (tail.length + 1) → Set (colouredOrderedEdgeLanguage A k).Symbol)
    (E : Set (Set X)) (κ : Type v) [Fintype κ] [Nonempty κ]
    (hSupportNonempty : Nonempty (OldACarrierEdge
      (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered B))
    (hSupportCovers : ∀ x, ∃ e : OldACarrierEdge
      (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered B, x ∈ e.1)
    (hAdjacent : T.AdjacentParameters Subtype.val (allowedByPredicates B symbols))
    (hCuts : ∀ j : Fin tail.length, LabelledGirthGT
      (T.wagonClassCarrier Subtype.val j.castSucc) (tail.get j))
    (hOrder : ProjectedOrderEverySpanningType.{v, v} tail) :
    UnrestrictedPredicateOrderWitness
      (colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))).ordered
      B tail T symbols ({s : Set X // s ∈ E} → κ) := by
  classical
  let W := ULift.{v} (Fin k)
  let Small : RelStructure (colouredOrderedEdgeLanguage A k) W :=
    colouredOrderedEdgeSource k (fun i => part (enumerate.symm (ULift.up i)))
  let Colours := {s : Set X // s ∈ E} → κ
  let : Nontrivial W := enumerate.injective.nontrivial
  let : Fintype Colours := Fintype.ofFinite Colours
  have hSpan : ∃ (r : (colouredOrderedEdgeLanguage A k).Symbol)
      (z : Fin ((colouredOrderedEdgeLanguage A k).arity r) → W),
        Small.rel r z ∧ Function.Surjective z := by
    refine ⟨.inl (.inl ()), ULift.up, ULift.up_injective, ?_⟩
    intro x
    exact ⟨x.down, rfl⟩
  have hAtZero : tail.get ⟨0, List.length_pos_iff.mpr ht.nonempty⟩ = tail.headD 0 := by
    cases tail with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons a rest => rfl
  have hGirth := ordinaryGirth_of_targetBottomLabelledCut Small.ordered B T (tail.headD 0)
    (hAtZero ▸ hCuts ⟨0, List.length_pos_iff.mpr ht.nonempty⟩)
  exact hOrder (colouredOrderedEdgeLanguage A k) Small hSpan Colours B hExtends
    T symbols hSupportNonempty hSupportCovers hGirth hAdjacent (fun j _ => hCuts j)

end StructuralRamsey.Girth.TrainRecursiveWitness
