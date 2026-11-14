import Girth.TrainRecursiveOneEdgeTarget

set_option autoImplicit false
set_option Elab.async false

/-!
# One-copy targets are the complementary case of two physical A-copies

The universal q>2 induction is formulated for targets with at least two
different physical A-copy carriers. To use it in the full circulation
theorem, its negation must be discharged rather than silently excluded.

For a covered target the failure of two different carriers makes the
physical support family a subsingleton. The *already verified* one-edge
constructor then supplies an actual OrderStage and its selected
DesignatedArrow for EVERY admissible cutoff vector and colour palette.

The obtained one-edge stage uses the canonical singleton identity base
family: this is a separate final-domain branch, not a proof of the
stronger arbitrary-base UniformSelectedPartiteForest predicate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB : Type v}

/-- If there are no two distinct physical A-copies, all actual support
carriers coincide. We do not assume uniqueness of A-embeddings: only
the equality of their image carriers is used. -/
theorem supportCopies_subsingleton_of_no_two
    (A : RelStructure L UA) (B : RelStructure L VB)
    (hNo : ¬ ∃ a b : Embedding A B, ¬ SameCopy a b) :
    (supportCopies A B).Subsingleton := by
  intro X hX Y hY
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  subst X
  subst Y
  have hs : SameCopy a b := by
    by_contra hne
    exact hNo ⟨a, b, hne⟩
  change copyCarrier a = copyCarrier b at hs
  exact hs

namespace TrainRecursiveWitness

/-- The negation of the nontrivial-target condition is handled by a
genuine selected OrderStage, retaining all original train relations
and original parameters without invoking any lower-rank operator. -/
theorem exists_orderStage_of_no_two_copies
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1)
    (κ : Type w)
    (hNo : ¬ ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b) :
    ∃ S : OrderStage A₀.ordered B B
        {Embedding.id B} t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ := by
  have hPhysical : (supportCopies A₀.ordered B).Subsingleton :=
    supportCopies_subsingleton_of_no_two A₀.ordered B hNo
  exact exists_orderStage_designatedArrow_of_oneEdgeTarget
    A₀ B t ht targetTrain allowed hPhysical
    hSupportNonempty hSupportCovers κ

/-- A genuine case split with NO one-copy precondition on the input:
either two different A-carriers exist, or the selected one-edge order
stage is already available. This is a reusable final-domain adapter
for the all-edge-type rank induction. -/
theorem two_copies_or_one_edge_order_stage
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB,
      ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1)
    (κ : Type w) :
    (∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b) ∨
      (∃ S : OrderStage A₀.ordered B B
          {Embedding.id B} t targetTrain allowed,
        DesignatedArrow S.toForestTailStage κ) := by
  by_cases hTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b
  · exact Or.inl hTwo
  · exact Or.inr
      (exists_orderStage_of_no_two_copies A₀ B t ht
        targetTrain allowed hSupportNonempty hSupportCovers κ hTwo)

end TrainRecursiveWitness
end StructuralRamsey.Girth
