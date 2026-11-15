import Girth.Track1ActualSelectedLiftPairwiseAllowed
import Girth.Track1PhysicalSelectedRepresentatives
import Girth.Track1ForbiddenPartDegreeOne

/-!
# Track 1: pairwise allowed intersections of real selected B-supports

Index selected B images by physical image carriers and choose a GENUINE
EHN-selected representative for each carrier. This avoids assuming
that the original selected embedding labels were physically injective
or citing any order-specific equality theorem.

The source B restricted-intersection condition supplies forbidden
degree one. The original EHN controlled carrier intersections give
the exact SAME physical A-edge in both selected B support pieces,
using Track1ControlledPhysicalIntersection.

No output allowed-intersection assumption is made.
DRAFT: exact-head Lean compilation and axiom audit pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I : Type v}

/-- Genuine, physically distinct selected B copies have allowed
intersections after splitting forbidden incidences. All owner
uniqueness and physical distinctness follow from the input source
and representative construction, rather than extra output axioms. -/
theorem track1_physicalActualSelectedLiftPairwiseAllowed
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Set (Embedding B C))
    (sourceColour : VB → I)
    (predicate : V → I) (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ supportCopies A B → f ∈ supportCopies A B → e ≠ f →
      ∀ w : VB, w ∈ e → w ∈ f → sourceColour w ∈ allowed)
    (hPredicate : ∀ b : Embedding B C, b ∈ family →
      ∀ w : VB, predicate (b w) = sourceColour w)
    (hControlled : ∀ b c : Embedding B C,
      b ∈ family → c ∈ family → ¬ SameCopy b c →
        (copyCarrier b ∩ copyCarrier c).Subsingleton ∨
          ∃ a : Embedding A C,
            copyCarrier b ∩ copyCarrier c = copyCarrier a) :
    let f : Track1PhysicalBCarrier family → Embedding B C :=
      track1_physicalRepresentative family
    PairwiseAllowed
      (fun q : Track1PhysicalBCarrier family =>
        (actualSelectedOwnerCopy A f predicate allowed q
          (track1_selectedForbiddenDegreeOne A f
            sourceColour predicate allowed hRestricted
            (fun i w => hPredicate (f i)
              (track1_physicalRepresentative_spec family i).1 w) q)
        ).selectedLiftSupportPiece) := by
  classical
  dsimp
  let f : Track1PhysicalBCarrier family → Embedding B C :=
    track1_physicalRepresentative family
  have hPred : ∀ q : Track1PhysicalBCarrier family, ∀ w : VB,
      predicate (f q w) = sourceColour w := by
    intro q w
    exact hPredicate (f q)
      (track1_physicalRepresentative_spec family q).1 w
  have hForbid :
      ∀ q : Track1PhysicalBCarrier family, ∀ (w : VB)
        (e g : {e : Set VB // e ∈ supportCopies A B}),
        predicate (f q w) ∉ allowed →
        w ∈ e.1 → w ∈ g.1 → e = g :=
    track1_selectedForbiddenDegreeOne A f
      sourceColour predicate allowed hRestricted hPred
  have hDifferent : ∀ ⦃i j : Track1PhysicalBCarrier family⦄,
      i ≠ j → ¬ SameCopy (f i) (f j) := by
    intro i j hij
    exact track1_physicalRepresentative_distinct family hij
  have hControlledF :
      ∀ i j : Track1PhysicalBCarrier family,
        ¬ SameCopy (f i) (f j) →
        (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
          ∃ a : Embedding A C,
            copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a := by
    intro i j hNe
    exact hControlled (f i) (f j)
      (track1_physicalRepresentative_spec family i).1
      (track1_physicalRepresentative_spec family j).1 hNe
  exact track1_actualSelectedLiftPairwiseAllowed
    A f predicate allowed hForbid hDifferent hControlledF

#print axioms StructuralRamsey.Girth.track1_physicalActualSelectedLiftPairwiseAllowed

end StructuralRamsey.Girth
