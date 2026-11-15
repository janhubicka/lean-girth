import Girth.Track1SelectedMixedLF2
import Girth.Track1PhysicalSelectedRepresentatives

/-!
# Track 1: actual local mixed LF2 from physically distinct selected B copies

Use the checked mixedForestThrough_two_of_strong_controlledFamily and
actualRecursiveMixedLocalForest through the already proved
Track1SelectedMixedLF2 bridge. Index genuine EHN selected B images by
their PHYSICAL CARRIERS rather than the embedding labels.

The representative family retains the selected Ramsey arrow (separate
Track1PhysicalSelectedRepresentatives theorem) and contains one
distinguished source embedding for each physical B-copy carrier.
No global B-order uniqueness lemma is needed. Ambient A-edges are
not pruned from the mixed-owner forest test.

DRAFT: exact-head Lean elaboration and axioms remain unverified.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W Z : Type v}

/-- EHN strongness, A-linearity and controlled intersections directly
yield the actual mixed LF2 on ALL B-owners and ambient A-edge owners,
after selecting one genuine B embedding per physical B-copy carrier. -/
theorem track1_orderedSelectedFamily_actualMixedLF2
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    (D : RelStructure L W)
    (family : Set (Embedding B D))
    (hLinear : ALinear A D)
    (hStrong : ∀ b : Embedding B D,
      b ∈ family → AStrong A D (copyCarrier b))
    (hControlled : ∀ b c : Embedding B D,
      b ∈ family → c ∈ family → ¬ SameCopy b c →
        (copyCarrier b ∩ copyCarrier c).Subsingleton ∨
          ∃ a : Embedding A D,
            copyCarrier b ∩ copyCarrier c = copyCarrier a)
    (E : RelStructure L Z)
    (core : Embedding D E)
    (e₀ e₁ : Set VB)
    (he₀ : e₀ ∈ supportCopies A B)
    (he₁ : e₁ ∈ supportCopies A B)
    (hne : e₀ ≠ e₁) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun q : Track1PhysicalBCarrier family =>
          (mappedStrongASupportEmbedding A
             (track1_physicalRepresentative family q)
             (hStrong _ (track1_physicalRepresentative_spec family q).1)
             core).supportPiece)
        (fun ce : {ce : Set Z //
          ce ∈ mappedSupportCopies A D E core} => ce.1)) 2 := by
  classical
  let f : Track1PhysicalBCarrier family → Embedding B D :=
    track1_physicalRepresentative family
  have hStrongF : ∀ q, AStrong A D (copyCarrier (f q)) := by
    intro q
    exact hStrong (f q) (track1_physicalRepresentative_spec family q).1
  have hControlledF : ∀ i j, ¬ SameCopy (f i) (f j) →
      (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
        ∃ a : Embedding A D,
          copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a := by
    intro i j hNe
    exact hControlled (f i) (f j)
      (track1_physicalRepresentative_spec family i).1
      (track1_physicalRepresentative_spec family j).1 hNe
  have hPieces : Function.Injective (fun q => bSupportPiece A (f q)) :=
    track1_physicalRepresentative_supportPieces_injective A family
  exact track1_actualMixedLF2_of_strong_controlled
    A f hLinear hStrongF hControlledF
      core hPieces e₀ e₁ he₀ he₁ hne

#print axioms StructuralRamsey.Girth.track1_orderedSelectedFamily_actualMixedLF2

end StructuralRamsey.Girth
