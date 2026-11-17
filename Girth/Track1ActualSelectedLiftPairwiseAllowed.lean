import Girth.Track1ControlledPhysicalIntersection
import Girth.Track1ForbiddenPartDegreeOne

/-!
# Track 1: the ACTUAL selected split B-support family has allowed intersections

The original EHN selected family has controlled relational B overlaps.
We already proved a common A-copy in the overlap factors through BOTH
genuine selected B embeddings, so the corresponding physical split
edge belongs to BOTH lifted B-support pieces.

This packages the actual pairwise allowed-intersection theorem without
postulating that the output lift has pairwise allowed intersections.
The selected B copy indices must represent distinct IMAGE carriers,
which is automatic for an injective family of ordered B embeddings.

STAGED DRAFT: not exact-head kernel-compiled.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- The full selected B-support pieces in the owner-split witness have
allowed intersections, exactly as required by ForestOfCopies. -/
theorem track1_actualSelectedLiftPairwiseAllowed
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (hForbidden : ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f)
    (hDifferent : ∀ ⦃i j : Choice⦄, i ≠ j →
      ¬ SameCopy (family i) (family j))
    (hControlled : ∀ i j : Choice,
      ¬ SameCopy (family i) (family j) →
      (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
        ∃ a : Embedding A C,
          copyCarrier (family i) ∩ copyCarrier (family j) =
            copyCarrier a) :
    PairwiseAllowed
      (fun c : Choice =>
        (actualSelectedOwnerCopy A family predicate allowed
          c (hForbidden c)).selectedLiftSupportPiece) := by
  classical
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed
      c (hForbidden c)
  have hOld : ∀ ⦃i j : Choice⦄, i ≠ j →
      (Set.range (selected i).embedding ∩
        Set.range (selected j).embedding).Subsingleton ∨
        ∃ f : H.OldEdge,
          Set.range (selected i).embedding ∩
            Set.range (selected j).embedding ⊆ f.1 ∧
          f ∈ Set.range (selected i).physicalEdge ∧
          f ∈ Set.range (selected j).physicalEdge := by
    intro i j hij
    rcases track1_controlled_selectedPhysicalIntersections
        A family predicate allowed hControlled i j (hDifferent hij) with
      hs | ⟨f, hSub, ⟨ei, hei⟩, ⟨ej, hej⟩⟩
    · exact Or.inl hs
    · refine Or.inr ⟨f, hSub, ?_, ?_⟩
      · refine ⟨ei, ?_⟩
        apply Subtype.ext
        exact hei
      · refine ⟨ej, ?_⟩
        apply Subtype.ext
        exact hej
  exact ColouredOwnerSelectedCopy.selectedLiftSupport_pairwiseAllowed
    selected hOld

#print axioms StructuralRamsey.Girth.track1_actualSelectedLiftPairwiseAllowed

end StructuralRamsey.Girth
