import Girth.IncidenceCompression
import Girth.ConstantOwnerPullback

/-! # Girth contradiction from standard-copy owners

This packages the logical core of the circulation proof for an untouched
subsystem.  A short Berge cycle is assigned a standard-copy owner edge by
edge.  If the owner word is constant, the cycle pulls back to the old
subsystem.  Otherwise cyclic run compression turns the owner changes into
forbidden incidence data in the local forest.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y ι : Type v}

/-- The owner-word dichotomy used in the untouched-subsystem girth proof. -/
theorem no_short_support_cycle_of_owner_forest
    (A : RelStructure L UA)
    (Old : RelStructure L X)
    (Whole : RelStructure L Y)
    [Fintype ι] [Nonempty ι]
    (standard : ι → RelStructure.Embedding Old Whole)
    {F : ι → HypergraphPiece Y}
    (hForest : ForestOfCopies F)
    (P : Set Y)
    (hPart : EdgesMeetPartAtMostOne F P)
    (g : ℕ)
    (hOld : GirthGT (supportCopies A Old) g)
    (c : BergeCycle (supportCopies A Whole))
    (hLen : c.length ≤ g)
    (owner : Fin c.length → ι)
    (hEdgeOwner :
      ∀ j, c.edge j ⊆ copyCarrier (standard (owner j)))
    (hBoundary :
      ∀ j, owner j ≠ owner (cyclicSucc j) →
        c.vertex j ∈
            ((F (owner j)).restrictCarrier P).carrier ∧
          c.vertex j ∈
            ((F (owner (cyclicSucc j))).restrictCarrier P).carrier) :
    False := by
  classical
  by_cases hConst : ∃ q : ι, ∀ j : Fin c.length, owner j = q
  · rcases hConst with ⟨q, hq⟩
    apply no_short_support_cycle_in_embedding
      A Old Whole (standard q) g hOld c hLen
    intro j
    simpa [hq j] using hEdgeOwner j
  · have hZero : 0 < c.length :=
      lt_of_lt_of_le (by decide) c.hlength
    let j0 : Fin c.length := ⟨0, hZero⟩
    have hNotAll :
        ¬ ∀ j : Fin c.length, owner j = owner j0 := by
      intro h
      exact hConst ⟨owner j0, h⟩
    push Not at hNotAll
    rcases hNotAll with ⟨j, hj⟩
    exact
      RawCyclicIncidenceData.no_nonconstant_owner_cycle_of_forest_part
        hForest P hPart c owner hBoundary
        ⟨j, j0, hj⟩

end StructuralRamsey.Girth
