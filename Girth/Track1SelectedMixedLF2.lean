import Girth.TrainRecursiveBaseRamsey
import Girth.ForestActualRecursiveSupport

/-!
# Track 1: selected local mixed LF2 for the actual cutoff-three picture

Combine two existing, previously checked interfaces:
1. mixedForestThrough_two_of_strong_controlledFamily supplies the complete
   mixed TWO-member forest on actual B-images and EVERY ambient A-edge.
2. actualRecursiveMixedLocalForest transports that honest finite-set
   invariant to labelled outer owners and one-edge core owners, after
   representative selection.

The assumptions that B has two distinct support edges and that the
selected B-support pieces have distinct carriers are explicit. These
are precisely the nontrivial/local-owner hypotheses for cutoff three.

DRAFT: exact-head Lean elaboration and #print axioms are pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Src Core Tgt I : Type v}

/-- The actual mixed previous-cutoff LF2 hypothesis follows from the
selected local witness's strongness, controlled intersections and A-linearity.
Every ambient core A-edge is included; no edge-coverage pruning occurs. -/
theorem track1_actualMixedLF2_of_strong_controlled
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {C : RelStructure L Core}
    {D : RelStructure L Tgt}
    (f : I → Embedding B C)
    (hLinear : ALinear A C)
    (hStrong : ∀ i, AStrong A C (copyCarrier (f i)))
    (hControlled : ∀ i j, ¬ SameCopy (f i) (f j) →
      (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
        ∃ a : Embedding A C,
          copyCarrier (f i) ∩ copyCarrier (f j) = copyCarrier a)
    (core : Embedding C D)
    (hCopies : Function.Injective (fun i => bSupportPiece A (f i)))
    (e₀ e₁ : Set VB)
    (he₀ : e₀ ∈ supportCopies A B)
    (he₁ : e₁ ∈ supportCopies A B)
    (hne : e₀ ≠ e₁) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun i => (mappedStrongASupportEmbedding A (f i) (hStrong i) core).supportPiece)
        (fun ce : {ce : Set Tgt // ce ∈ mappedSupportCopies A C D core} => ce.1))
      2 := by
  have hFinite : FiniteMixedForestThrough
      (RelationalMixedSupportTest A f) 2 :=
    mixedForestThrough_two_of_strong_controlledFamily
      A f hLinear hStrong hControlled
  exact actualRecursiveMixedLocalForest
    A f hStrong core hCopies e₀ e₁ he₀ he₁ hne 2 hFinite

#print axioms StructuralRamsey.Girth.track1_actualMixedLF2_of_strong_controlled

end StructuralRamsey.Girth
