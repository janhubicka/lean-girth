import Girth.ForestActualRecursiveSupport
import Girth.Support

/-!
# Numbered Track 1: injective selected physical B owners from a genuine order

For the local-forest partite lemma the selected B target is given its
original global auxiliary linear order BEFORE EHN. Distinct embeddings
of a finite linearly ordered B with the same IMAGE CARRIER are equal.
Therefore any injectively indexed set of genuine B embeddings already
has distinct full physical B-support pieces; no new choice of
representative or extra duplicate-owner axiom is needed.

For un-ordered target languages, the checked general
physicalSupportRepresentative machinery is still the safe alternative.

STAGED DRAFT, not kernel-compiled on this branch.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V Choice : Type v}

/-- The image-carrier map of an injectively indexed selected family of
globally ordered B copies is injective, even if the ambient order
relation outside the copies is not itself a linear order. -/
theorem orderedB_selectedCarriers_injective
    (B₀ : RelStructure L VB)
    (D : RelStructure L.withOrder V)
    [LinearOrder VB] [Finite VB]
    (family : Choice → Embedding B₀.ordered D)
    (hFamily : Function.Injective family) :
    Function.Injective (fun i : Choice => copyCarrier (family i)) := by
  intro i j hCarrier
  apply hFamily
  exact ordered_embedding_eq_of_sameCopy (family i) (family j) hCarrier

/-- More precisely, the COMPLETE B-support pieces of these selected
copies have distinct physical labels, including any isolated vertices
of their carriers. This is the exact \`hCopies\` input to
\`actualRecursiveMixedLocalForest\`. -/
theorem orderedB_selectedSupportPieces_injective
    (A : RelStructure L.withOrder UA)
    (B₀ : RelStructure L VB)
    (D : RelStructure L.withOrder V)
    [LinearOrder VB] [Finite VB]
    (family : Choice → Embedding B₀.ordered D)
    (hFamily : Function.Injective family) :
    Function.Injective (fun i : Choice => bSupportPiece A (family i)) := by
  intro i j hPiece
  apply hFamily
  have hCarrier : SameCopy (family i) (family j) := by
    exact congrArg HypergraphPiece.carrier hPiece
  exact ordered_embedding_eq_of_sameCopy (family i) (family j) hCarrier

#print axioms StructuralRamsey.Girth.orderedB_selectedCarriers_injective
#print axioms StructuralRamsey.Girth.orderedB_selectedSupportPieces_injective

end StructuralRamsey.Girth
