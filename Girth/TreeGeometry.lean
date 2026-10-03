import Girth.SupportedTree

/-! # Abstract geometry consequences for the girth proof

This file factors the logical consequences used in Lemma 2.1 away from the
recursive tree-amalgam construction.  The remaining recursive obligation is
then concentrated in the pairwise intersection predicate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- Every ambient copy of `A` is contained in some ambient copy of `B`. -/
def ACopiesCoveredByB
    (A : RelStructure L U) (B : RelStructure L V)
    (T : RelStructure L W) : Prop :=
  ∀ a : Embedding A T, ∃ b : Embedding B T,
    copyCarrier a ⊆ copyCarrier b

/-- Distinct `B`-copy carriers meet in at most one vertex or exactly in the
carrier of an `A`-copy.  The separate singleton-support clause of the paper
will be added when the recursive intersection theorem is formalized. -/
def BIntersectionsControlled
    (A : RelStructure L U) (B : RelStructure L V)
    (T : RelStructure L W) : Prop :=
  ∀ b₁ b₂ : Embedding B T, ¬ SameCopy b₁ b₂ →
    (copyCarrier b₁ ∩ copyCarrier b₂).Subsingleton ∨
      ∃ a : Embedding A T,
        copyCarrier b₁ ∩ copyCarrier b₂ = copyCarrier a

/-- The generic tree-amalgam localization theorem supplies `A`-copy coverage
by `B`-copies for every supported tree amalgam. -/
theorem ASupportedTreeAmalgam.aCopiesCoveredByB
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hA : A.Irreducible)
    (hT : ASupportedTreeAmalgam A B W T) :
    ACopiesCoveredByB A B T := by
  intro a
  obtain ⟨b, hab⟩ := hT.aCopy_contained_in_copy hA a
  refine ⟨b, ?_⟩
  intro x hx
  rcases hx with ⟨u, rfl⟩
  obtain ⟨v, huv⟩ := hab u
  exact ⟨v, huv.symm⟩

/-- Once global `A`-linearity and pairwise `B`-intersection control are
known, every `B`-copy is automatically `A`-strong.  This is the formal
version of the simplification used in the reorganized proof of Lemma 2.1. -/
theorem aStrong_of_linear_and_controlled
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hLinear : ALinear A T)
    (hCover : ACopiesCoveredByB A B T)
    (hInter : BIntersectionsControlled A B T)
    (b : Embedding B T) :
    AStrong A T (copyCarrier b) := by
  intro a hMeet
  obtain ⟨b', hab'⟩ := hCover a
  by_cases hSameB : SameCopy b' b
  · intro x hx
    have hx' : x ∈ copyCarrier b' := hab' hx
    rw [hSameB] at hx'
    exact hx'
  · rcases hInter b' b hSameB with hSmall | ⟨c, hc⟩
    · have hs : (copyCarrier a ∩ copyCarrier b).Subsingleton := by
        intro x hx y hy
        apply hSmall
        · exact ⟨hab' hx.1, hx.2⟩
        · exact ⟨hab' hy.1, hy.2⟩
      exact (hMeet hs).elim
    · by_cases hSameA : SameCopy a c
      · intro x hx
        have hxc : x ∈ copyCarrier c := by
          rw [← hSameA]
          exact hx
        have hxboth : x ∈ copyCarrier b' ∩ copyCarrier b := by
          rw [hc]
          exact hxc
        exact hxboth.2
      · have hSmallAC := hLinear a c hSameA
        have hs : (copyCarrier a ∩ copyCarrier b).Subsingleton := by
          intro x hx y hy
          apply hSmallAC
          · refine ⟨hx.1, ?_⟩
            have hxboth : x ∈ copyCarrier b' ∩ copyCarrier b :=
              ⟨hab' hx.1, hx.2⟩
            rw [hc] at hxboth
            exact hxboth
          · refine ⟨hy.1, ?_⟩
            have hyboth : y ∈ copyCarrier b' ∩ copyCarrier b :=
              ⟨hab' hy.1, hy.2⟩
            rw [hc] at hyboth
            exact hyboth
        exact (hMeet hs).elim

end StructuralRamsey.Girth
