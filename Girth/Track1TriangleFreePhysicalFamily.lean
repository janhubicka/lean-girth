import Girth.Track1PhysicalSelectedRepresentatives
import Girth.Track1TriangleFreeSelectedFamily

/-!
# Track 1 — triangle-free EHN with one indexed copy per physical B carrier

The already kernel-checked triangle-free EHN theorem returns the genuine
fresh-order-preserving *set* of full B embeddings. Normalize that set by
its physical B-copy carriers, choosing one of its original full
embeddings for each carrier.

This preserves the selected Ramsey arrow EVEN IF the source B is not
rigid: any A-copy inside one B image factors through any other full
B embedding onto the same induced image carrier. It supplies a
physically injective complete B-support family and avoids an
unproved ordered-embedding uniqueness lemma.

No new coloured-witness or partite-fusion assertion is made here.
DRAFT: not yet Lean-compiled on this continuation branch.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB : Type v}

/-- The exact EHN triangle-free local witness with a physically
distinct selected B-family retaining the original ordered arrow. -/
theorem track1_triangleFreeRamsey_physicalSelectedFamily
    (A : RelStructure L UA) (B : RelStructure L VB)
    [LinearOrder UA] [LinearOrder VB]
    [Finite UA] [Finite VB]
    (hA : A.Irreducible)
    (hBlin : ALinear A B)
    (hBgirth : GirthGT (supportCopies A B) 3)
    (hmono : ∀ a : Embedding A B, StrictMono a)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
        (C : StructuralRamsey.Structure (closureLanguage L) W)
        (J : Type v) (f : J → Embedding B (closureRelReduct C)),
      ElementaryCAThreeClass A C ∧
      Function.Injective (fun j : J => bSupportPiece A (f j)) ∧
      (∀ j : J, ∀ x y : VB, x < y →
        @LT.lt W o.toLT (f j x) (f j y)) ∧
      (∀ j : J, AStrong A (closureRelReduct C) (copyCarrier (f j))) ∧
      (∀ i j : J, i ≠ j →
        (copyCarrier (f i) ∩ copyCarrier (f j)).Subsingleton ∨
          ∃ a : Embedding A (closureRelReduct C),
            copyCarrier (f i) ∩ copyCarrier (f j) =
              copyCarrier a) ∧
      (∀ χ : Embedding A (closureRelReduct C) → κ,
        ∃ j : J, ∀ a₁ a₂ : Embedding A B,
          χ ((f j).comp a₁) = χ ((f j).comp a₂)) := by
  classical
  obtain ⟨W, hW, o, C, family, hC, hOrder, hStrong,
      hControlled, hRamsey⟩ :=
    track1_selectedOrderedRamseyFamily_triangleFree
      A B hA hBlin hBgirth hmono κ
  let J : Type v := Track1PhysicalBCarrier family
  let f : J → Embedding B (closureRelReduct C) :=
    track1_physicalRepresentative family
  refine ⟨W, hW, o, C, J, f, hC, ?_, ?_, ?_, ?_, ?_⟩
  · exact track1_physicalRepresentative_supportPieces_injective
      A family
  · intro j x y hxy
    exact hOrder (f j)
      (track1_physicalRepresentative_spec family j).1 x y hxy
  · intro j
    exact hStrong (f j)
      (track1_physicalRepresentative_spec family j).1
  · intro i j hij
    have hDifferent : ¬ SameCopy (f i) (f j) :=
      track1_physicalRepresentative_distinct family hij
    exact hControlled (f i)
      (track1_physicalRepresentative_spec family i).1
      (f j)
      (track1_physicalRepresentative_spec family j).1
      hDifferent
  · exact track1_physicalRepresentative_arrow A family hRamsey

#print axioms StructuralRamsey.Girth.track1_triangleFreeRamsey_physicalSelectedFamily

end StructuralRamsey.Girth
