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

/-- The two side images of a concrete free amalgam intersect exactly in
the image of the prescribed overlap. -/
theorem freeAmalgam_side_intersection
    {D : RelStructure L U} {Left : RelStructure L V}
    {Right : RelStructure L W} {X : Type v}
    {Whole : RelStructure L X}
    {fL : Embedding D Left} {fR : Embedding D Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam fL fR iL iR) :
    Set.range iL ∩ Set.range iR = Set.range (iL.comp fL) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx.1 with ⟨l, hl⟩
    rcases hx.2 with ⟨r, hr⟩
    have hlr : iL l = iR r := hl.symm.trans hr
    obtain ⟨d, hld, hrd⟩ := (hfree.overlap l r).mp hlr
    refine ⟨d, ?_⟩
    change iL (fL d) = x
    rw [← hld]
    exact hl
  · intro x hx
    rcases hx with ⟨d, rfl⟩
    constructor
    · exact ⟨fL d, rfl⟩
    · refine ⟨fR d, ?_⟩
      exact (hfree.overlap (fL d) (fR d)).mpr ⟨d, rfl, rfl⟩

/-- An embedded irreducible structure in a free amalgam factors through one
side, with exactly the same image carrier. -/
theorem irreducibleCopy_side_of_freeAmalgam
    {D : RelStructure L U} {Left : RelStructure L V}
    {Right : RelStructure L W} {X Y : Type v}
    {Whole : RelStructure L X} {Q : RelStructure L Y}
    {fL : Embedding D Left} {fR : Embedding D Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam fL fR iL iR)
    (hQ : Q.Irreducible) (e : Embedding Q Whole) :
    (∃ eL : Embedding Q Left, SameCopy e (iL.comp eL)) ∨
      (∃ eR : Embedding Q Right, SameCopy e (iR.comp eR)) := by
  classical
  rcases hfree.irreducible_side (Set.range e) (hQ.range_embedding e) with hL | hR
  · let eL : Embedding Q Left :=
      e.factorThroughRange iL (fun q => hL ⟨e q, ⟨q, rfl⟩⟩)
    have heL (q : Y) : e q = iL (eL q) :=
      Classical.choose_spec (hL ⟨e q, ⟨q, rfl⟩⟩)
    refine Or.inl ⟨eL, ?_⟩
    change Set.range e = Set.range (iL.comp eL)
    apply Set.Subset.antisymm
    · rintro x ⟨q, rfl⟩
      exact ⟨q, (heL q).symm⟩
    · rintro x ⟨q, rfl⟩
      exact ⟨q, heL q⟩
  · let eR : Embedding Q Right :=
      e.factorThroughRange iR (fun q => hR ⟨e q, ⟨q, rfl⟩⟩)
    have heR (q : Y) : e q = iR (eR q) :=
      Classical.choose_spec (hR ⟨e q, ⟨q, rfl⟩⟩)
    refine Or.inr ⟨eR, ?_⟩
    change Set.range e = Set.range (iR.comp eR)
    apply Set.Subset.antisymm
    · rintro x ⟨q, rfl⟩
      exact ⟨q, (heR q).symm⟩
    · rintro x ⟨q, rfl⟩
      exact ⟨q, heR q⟩

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

/-- If two ambient `A`-copies lie in one `B`-copy and meet in more
than one vertex, linearity of `A` inside `B` forces them to have the same
carrier. -/
theorem sameCopy_of_contained_and_not_subsingleton
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hBase : ALinear A B)
    (a c : Embedding A T) (b : Embedding B T)
    (ha : copyCarrier a ⊆ copyCarrier b)
    (hc : copyCarrier c ⊆ copyCarrier b)
    (hMeet : ¬ (copyCarrier a ∩ copyCarrier c).Subsingleton) :
    SameCopy a c := by
  classical
  let fa : Embedding A B := a.factorThroughRange b (fun x => ha ⟨x, rfl⟩)
  let fc : Embedding A B := c.factorThroughRange b (fun x => hc ⟨x, rfl⟩)
  have hfa (x : U) : a x = b (fa x) :=
    Classical.choose_spec (ha ⟨x, rfl⟩)
  have hfc (x : U) : c x = b (fc x) :=
    Classical.choose_spec (hc ⟨x, rfl⟩)
  by_contra hSame
  have hFactors : ¬ SameCopy fa fc := by
    intro h
    apply hSame
    change Set.range a = Set.range c
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨u, rfl⟩
      have hmem : fa u ∈ copyCarrier fc := by
        rw [← h]
        exact ⟨u, rfl⟩
      rcases hmem with ⟨v, huv⟩
      refine ⟨v, ?_⟩
      calc
        a u = b (fa u) := hfa u
        _ = b (fc v) := congrArg b huv
        _ = c v := (hfc v).symm
    · intro x hx
      rcases hx with ⟨u, rfl⟩
      have hmem : fc u ∈ copyCarrier fa := by
        rw [h]
        exact ⟨u, rfl⟩
      rcases hmem with ⟨v, huv⟩
      refine ⟨v, ?_⟩
      calc
        c u = b (fc u) := hfc u
        _ = b (fa v) := congrArg b huv
        _ = a v := (hfa v).symm
  have hSmallBase := hBase fa fc hFactors
  apply hMeet
  intro x hx y hy
  rcases hx.1 with ⟨ux, rfl⟩
  rcases hx.2 with ⟨vx, hvx⟩
  rcases hy.1 with ⟨uy, rfl⟩
  rcases hy.2 with ⟨vy, hvy⟩
  have hxB : fa ux = fc vx := by
    apply b.injective
    calc
      b (fa ux) = a ux := (hfa ux).symm
      _ = c vx := hvx
      _ = b (fc vx) := hfc vx
  have hyB : fa uy = fc vy := by
    apply b.injective
    calc
      b (fa uy) = a uy := (hfa uy).symm
      _ = c vy := hvy
      _ = b (fc vy) := hfc vy
  have hEq : fa ux = fa uy := hSmallBase
    ⟨⟨ux, rfl⟩, ⟨vx, hxB.symm⟩⟩
    ⟨⟨uy, rfl⟩, ⟨vy, hyB.symm⟩⟩
  exact a.injective (fa.injective hEq)

/-- Local `A`-linearity inside `B`, together with coverage and controlled
pairwise `B`-intersections, implies global `A`-linearity. -/
theorem aLinear_of_base_and_controlled
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hBase : ALinear A B)
    (hCover : ACopiesCoveredByB A B T)
    (hInter : BIntersectionsControlled A B T) :
    ALinear A T := by
  intro a₁ a₂ hne
  by_contra hMeet
  obtain ⟨b₁, ha₁⟩ := hCover a₁
  obtain ⟨b₂, ha₂⟩ := hCover a₂
  by_cases hSameB : SameCopy b₁ b₂
  · have ha₂' : copyCarrier a₂ ⊆ copyCarrier b₁ := by
      intro x hx
      have : x ∈ copyCarrier b₂ := ha₂ hx
      rw [← hSameB] at this
      exact this
    exact hne (sameCopy_of_contained_and_not_subsingleton
      hBase a₁ a₂ b₁ ha₁ ha₂' hMeet)
  · rcases hInter b₁ b₂ hSameB with hSmall | ⟨c, hc⟩
    · apply hMeet
      intro x hx y hy
      apply hSmall
      · exact ⟨ha₁ hx.1, ha₂ hx.2⟩
      · exact ⟨ha₁ hy.1, ha₂ hy.2⟩
    · have hCommonSubset (x : W)
          (hx : x ∈ copyCarrier a₁ ∩ copyCarrier a₂) :
          x ∈ copyCarrier c := by
        have hxB : x ∈ copyCarrier b₁ ∩ copyCarrier b₂ :=
          ⟨ha₁ hx.1, ha₂ hx.2⟩
        rw [hc] at hxB
        exact hxB
      have hMeet₁ : ¬ (copyCarrier a₁ ∩ copyCarrier c).Subsingleton := by
        intro hs
        apply hMeet
        intro x hx y hy
        exact hs ⟨hx.1, hCommonSubset x hx⟩
          ⟨hy.1, hCommonSubset y hy⟩
      have hMeet₂ : ¬ (copyCarrier a₂ ∩ copyCarrier c).Subsingleton := by
        intro hs
        apply hMeet
        intro x hx y hy
        exact hs ⟨hx.2, hCommonSubset x hx⟩
          ⟨hy.2, hCommonSubset y hy⟩
      have hc₁ : copyCarrier c ⊆ copyCarrier b₁ := by
        intro x hx
        have : x ∈ copyCarrier b₁ ∩ copyCarrier b₂ := by
          rw [hc]
          exact hx
        exact this.1
      have hc₂ : copyCarrier c ⊆ copyCarrier b₂ := by
        intro x hx
        have : x ∈ copyCarrier b₁ ∩ copyCarrier b₂ := by
          rw [hc]
          exact hx
        exact this.2
      have h1 := sameCopy_of_contained_and_not_subsingleton
        hBase a₁ c b₁ ha₁ hc₁ hMeet₁
      have h2 := sameCopy_of_contained_and_not_subsingleton
        hBase a₂ c b₂ ha₂ hc₂ hMeet₂
      exact hne (h1.trans h2.symm)

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
