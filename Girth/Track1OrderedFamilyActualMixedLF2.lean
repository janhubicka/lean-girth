import Girth.Track1SelectedMixedLF2
import Girth.Track1OrderedPhysicalOwners

/-!
# Track 1: actual local mixed LF2 from one selected ORDERED family

Compose the previously checked mixed-forest pair theorem with actual
owner transport and the fact that an injective family of finite ordered
B embeddings has distinct physical B-support carriers.

The selected family is the exact subtype of an arbitrary set of
genuinely ordered B embeddings. No choice of duplicate support
representatives, no invented mixed-LF2 premise, and no deletion of
ambient A-edges is needed.

This is a conditional theorem. A selected ordered EHN Ramsey
family supplies its hypotheses in the next integration step.

STAGED DRAFT: not kernel-checked on this branch.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W Z : Type v}

/-- The genuine ordered selected family, strongness, and pairwise
intersection control give exactly the local mixed LF2 required
in the true-active three-member picture extension. -/
theorem track1_orderedSelectedFamily_actualMixedLF2
    (A : RelStructure L.withOrder UA)
    (B₀ : RelStructure L VB)
    (D : RelStructure L.withOrder W)
    [LinearOrder VB] [Finite VB]
    (family : Set (Embedding B₀.ordered D))
    (hLinear : ALinear A D)
    (hStrong : ∀ b : Embedding B₀.ordered D,
      b ∈ family → AStrong A D (copyCarrier b))
    (hControlled : ∀ b c : Embedding B₀.ordered D,
      b ∈ family → c ∈ family → ¬ SameCopy b c →
        (copyCarrier b ∩ copyCarrier c).Subsingleton ∨
          ∃ a : Embedding A D,
            copyCarrier b ∩ copyCarrier c = copyCarrier a)
    (E : RelStructure L.withOrder Z)
    (core : Embedding D E)
    (e₀ e₁ : Set VB)
    (he₀ : e₀ ∈ supportCopies A B₀.ordered)
    (he₁ : e₁ ∈ supportCopies A B₀.ordered)
    (hne : e₀ ≠ e₁) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun i : {b : Embedding B₀.ordered D // b ∈ family} =>
          (mappedStrongASupportEmbedding A i.1
             (hStrong i.1 i.2) core).supportPiece)
        (fun ce : {ce : Set Z //
          ce ∈ mappedSupportCopies A D E core} => ce.1)) 2 := by
  classical
  let f : {b : Embedding B₀.ordered D // b ∈ family} →
      Embedding B₀.ordered D := fun i => i.1
  have hfInj : Function.Injective f := by
    intro i j h
    exact Subtype.ext h
  have hStrongF : ∀ i, AStrong A D (copyCarrier (f i)) :=
    fun i => hStrong i.1 i.2
  have hControlledF : ∀ i j, ¬ SameCopy (f i) (f j) →
      (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
        ∃ a : Embedding A D,
          copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a := by
    intro i j hij
    exact hControlled i.1 j.1 i.2 j.2 hij
  have hPieces : Function.Injective (fun i => bSupportPiece A (f i)) :=
    orderedB_selectedSupportPieces_injective A B₀ D f hfInj
  exact track1_actualMixedLF2_of_strong_controlled
    A f hLinear hStrongF hControlledF
      core hPieces e₀ e₁ he₀ he₁ hne

#print axioms StructuralRamsey.Girth.track1_orderedSelectedFamily_actualMixedLF2

end StructuralRamsey.Girth
