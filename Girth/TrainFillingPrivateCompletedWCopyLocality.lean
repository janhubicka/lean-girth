import Girth.TrainFillingPrivateCompletedOrderedW

set_option Elab.async false

/-!
# Complete A-copy locality in the order-completed first-wagon W

The raw disjoint union cannot be embedded inducedly into a fully
within-colour ordered target. For the completed W, however, adding
cross-summand order comparisons creates no cross-summand A-copy:
every copy of the genuine k-vertex coloured edge source has a
spanning k-edge, and that edge is still componentwise in W.

This is the first local bridge towards transporting the EHN
selected-arrow from the completed W. It does NOT assert that the
component inclusions are full induced embeddings or that a
covered/marked EHN witness has been produced.

Uncompiled Lean source candidate. No admissions/new axioms.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V P : Type v}

/-- Every actual A-small copy in the completed ordered W is supported
on ONE original first-wagon summand. The added cross-summand
within-colour comparisons produce no new k-edge copies. -/
theorem completedFirstWagon_ACopy_in_one_summand
    [LinearOrder I] [LinearOrder V] [LinearOrder P]
    (k : ℕ) (profile : Fin k → I)
    (oldEdges : Set (Set V)) (oldColour : V → I)
    (oldCarrier : P → Set V)
    (a : Embedding
      (colouredOrderedEdgeSource.{u,v} k profile)
      (completedFirstWagonColouredUnion k oldEdges oldColour oldCarrier)) :
    ∃ p : P, ∀ x : ULift.{v} (Fin k),
      ∃ y : {z : V // z ∈ oldCarrier p},
        a x = (⟨p, y⟩ : FirstWagonUnionVertex oldCarrier) := by
  let t : Fin k → FirstWagonUnionVertex oldCarrier :=
    fun j => a (ULift.up j)
  have hRel :
      (completedFirstWagonColouredUnion k oldEdges
        oldColour oldCarrier).rel (.inl (.inl ())) t := by
    have hSource :
        (colouredOrderedEdgeSource.{u,v} k profile).rel
          (.inl (.inl ()))
          (fun j : Fin k => ULift.up j) := by
      change Function.Injective (fun j : Fin k => ULift.up j)
      intro x y h
      exact congrArg ULift.down h
    exact (a.map_rel_iff (.inl (.inl ()))
      (fun j : Fin k => ULift.up j)).mpr hSource
  obtain ⟨p, hp⟩ :=
    completedFirstWagon_edge_in_one_summand k oldEdges
      oldColour oldCarrier t hRel
  refine ⟨p, ?_⟩
  intro x
  cases x with
  | up j => exact hp j

end StructuralRamsey.Girth
