import Girth.ForestStar
import Girth.SupportForestToTree

/-! # Forest completion inside one designated B-component

The initial-picture completion argument is local inside each disjoint B-copy:
the B-support piece is the centre and selected A-copies are one-edge leaves.
A-linearity supplies the pairwise leaf intersections.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W J : Type v}

/-- One B-support piece together with finitely labelled, pairwise distinct
contained A-copies is a forest.  This is the exact local star used in the
initial-picture completion proof. -/
theorem forest_bSupport_with_aLeaves
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    (b : Embedding B R)
    (a : J → Embedding A R)
    (hLinear : ALinear A R)
    (hSub : ∀ j : J, copyCarrier (a j) ⊆ copyCarrier b)
    (hDistinct :
      ∀ ⦃i j : J⦄, i ≠ j → ¬ SameCopy (a i) (a j)) :
    ForestOfCopies
      (centerWithEdgeLeaves
        (bSupportPiece A b)
        (fun j => copyCarrier (a j))) := by
  apply forest_centerWithEdgeLeaves
  · intro j
    exact ⟨a j, rfl, hSub j⟩
  · intro i j hij
    exact hLinear (a i) (a j) (hDistinct hij)

end StructuralRamsey.Girth
