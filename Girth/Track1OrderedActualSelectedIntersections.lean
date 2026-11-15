import Girth.Track1ActualSelectedLiftPairwiseAllowed
import Girth.Track1OrderedPhysicalOwners

/-!
# Track 1: ordered EHN selected copies have actual allowed lifted intersections

An injectively indexed family of genuine finite ordered B embeddings
automatically has distinct IMAGE carriers.  The source B
allowed-predicate edge-intersection property gives forbidden degree
one, and actual selected B predicate preservation transports it.

Consequently the checked owner-splitting construction produces a
family of full B-support pieces with pairwise AllowedIntersection.
No output intersection hypothesis or choice of physical representatives
is needed. The remaining old colour/order presentation adapter is
stated separately.

STAGED DRAFT: not kernel-compiled yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- The entire actual lifted *ordered* selected B-support family
inherits allowed pairwise intersections, using only the standard
old selected-family and source-incidence hypotheses. -/
theorem track1_orderedActualSelectedLiftPairwiseAllowed
    (A : RelStructure L.withOrder UA)
    (B₀ : RelStructure L VB)
    (D : RelStructure L.withOrder V)
    [LinearOrder VB] [Finite VB]
    (family : Choice → Embedding B₀.ordered D)
    (hFamily : Function.Injective family)
    (sourceColour : VB → I)
    (predicate : V → I) (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ supportCopies A B₀.ordered →
      f ∈ supportCopies A B₀.ordered → e ≠ f →
      ∀ w : VB, w ∈ e → w ∈ f → sourceColour w ∈ allowed)
    (hPredicate : ∀ c : Choice, ∀ w : VB,
      predicate (family c w) = sourceColour w)
    (hControlled : ∀ i j : Choice,
      ¬ SameCopy (family i) (family j) →
      (copyCarrier (family i) ∩ copyCarrier (family j)).Subsingleton ∨
        ∃ a : Embedding A D,
          copyCarrier (family i) ∩ copyCarrier (family j) =
            copyCarrier a) :
    PairwiseAllowed
      (fun c : Choice =>
        (actualSelectedOwnerCopy A family predicate allowed c
          (track1_selectedForbiddenDegreeOne A family
            sourceColour predicate allowed hRestricted hPredicate c)).selectedLiftSupportPiece) := by
  classical
  have hDifferent : ∀ ⦃i j : Choice⦄, i ≠ j →
      ¬ SameCopy (family i) (family j) := by
    intro i j hij hsame
    exact hij ((orderedB_selectedCarriers_injective
      B₀ D family hFamily) hsame)
  have hForbid :
      ∀ c : Choice, ∀ (w : VB)
        (e f : {e : Set VB // e ∈ supportCopies A B₀.ordered}),
        predicate (family c w) ∉ allowed →
        w ∈ e.1 → w ∈ f.1 → e = f :=
    track1_selectedForbiddenDegreeOne A family
      sourceColour predicate allowed hRestricted hPredicate
  exact track1_actualSelectedLiftPairwiseAllowed
    A family predicate allowed hForbid hDifferent hControlled

#print axioms StructuralRamsey.Girth.track1_orderedActualSelectedLiftPairwiseAllowed

end StructuralRamsey.Girth
