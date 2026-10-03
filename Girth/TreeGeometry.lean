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

/-- Equality of copy carriers is preserved by composition with an
ambient embedding. -/
theorem sameCopy_comp
    {A : RelStructure L U} {T : RelStructure L V}
    {S : RelStructure L W}
    {e f : Embedding A T} (h : SameCopy e f)
    (i : Embedding T S) :
    SameCopy (i.comp e) (i.comp f) := by
  change Set.range (i.comp e) = Set.range (i.comp f)
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    have : e a ∈ copyCarrier f := by
      rw [← h]
      exact ⟨a, rfl⟩
    rcases this with ⟨b, hab⟩
    exact ⟨b, congrArg i hab⟩
  · rintro x ⟨a, rfl⟩
    have : f a ∈ copyCarrier e := by
      rw [h]
      exact ⟨a, rfl⟩
    rcases this with ⟨b, hab⟩
    exact ⟨b, congrArg i hab⟩

/-- A controlled pair of `B`-copies remains controlled after embedding the
whole ambient structure. -/
theorem controlledIntersection_comp
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W} {X : Type v}
    {S : RelStructure L X}
    (hInter : BIntersectionsControlled A B T)
    (i : Embedding T S)
    (b₁ b₂ : Embedding B T)
    (hne : ¬ SameCopy (i.comp b₁) (i.comp b₂)) :
    (copyCarrier (i.comp b₁) ∩ copyCarrier (i.comp b₂)).Subsingleton ∨
      ∃ a : Embedding A S,
        copyCarrier (i.comp b₁) ∩ copyCarrier (i.comp b₂) =
          copyCarrier a := by
  have hneOld : ¬ SameCopy b₁ b₂ := by
    intro h
    exact hne (sameCopy_comp h i)
  rcases hInter b₁ b₂ hneOld with hSmall | ⟨a, ha⟩
  · left
    intro x hx y hy
    rcases hx.1 with ⟨u₁, hu₁⟩
    rcases hx.2 with ⟨u₂, hu₂⟩
    rcases hy.1 with ⟨v₁, hv₁⟩
    rcases hy.2 with ⟨v₂, hv₂⟩
    have hxu : b₁ u₁ = b₂ u₂ := by
      apply i.injective
      exact hu₁.symm.trans hu₂
    have hyv : b₁ v₁ = b₂ v₂ := by
      apply i.injective
      exact hv₁.symm.trans hv₂
    have hold : b₁ u₁ = b₁ v₁ := hSmall
      ⟨⟨u₁, rfl⟩, ⟨u₂, hxu.symm⟩⟩
      ⟨⟨v₁, rfl⟩, ⟨v₂, hyv.symm⟩⟩
    calc
      x = i (b₁ u₁) := hu₁.symm
      _ = i (b₁ v₁) := congrArg i hold
      _ = y := hv₁
  · right
    refine ⟨i.comp a, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx.1 with ⟨u₁, hu₁⟩
      rcases hx.2 with ⟨u₂, hu₂⟩
      have hxu : b₁ u₁ = b₂ u₂ := by
        apply i.injective
        exact hu₁.symm.trans hu₂
      have hold : b₁ u₁ ∈ copyCarrier a := by
        rw [← ha]
        exact ⟨⟨u₁, rfl⟩, ⟨u₂, hxu.symm⟩⟩
      rcases hold with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      calc
        i (a v) = i (b₁ u₁) := congrArg i hv.symm
        _ = x := hu₁
    · intro x hx
      rcases hx with ⟨v, rfl⟩
      have hold : a v ∈ copyCarrier b₁ ∩ copyCarrier b₂ := by
        rw [ha]
        exact ⟨v, rfl⟩
      rcases hold.1 with ⟨u₁, hu₁⟩
      rcases hold.2 with ⟨u₂, hu₂⟩
      constructor
      · exact ⟨u₁, congrArg i hu₁.symm⟩
      · exact ⟨u₂, congrArg i hu₂.symm⟩

/-- In an `A`-edge free gluing, the intersection of an old `B`-copy
with the fresh side is controlled by the old `B`-intersection invariant.
This is the only nontrivial cross-side step in the recursive intersection
proof for supported tree amalgams. -/
theorem crossControlled_glueA
    {A : RelStructure L U} {B : RelStructure L V}
    {Old : RelStructure L W} {X : Type v}
    {Whole : RelStructure L X}
    (hBase : ALinear A B)
    (hCover : ACopiesCoveredByB A B Old)
    (hInter : BIntersectionsControlled A B Old)
    (fOld : Embedding A Old) (fB : Embedding A B)
    (iOld : Embedding Old Whole) (iB : Embedding B Whole)
    (hfree : IsFreeAmalgam fOld fB iOld iB)
    (cOld : Embedding B Old) :
    (copyCarrier (iOld.comp cOld) ∩ copyCarrier iB).Subsingleton ∨
      ∃ a : Embedding A Whole,
        copyCarrier (iOld.comp cOld) ∩ copyCarrier iB =
          copyCarrier a := by
  classical
  obtain ⟨b₀, hf₀⟩ := hCover fOld
  have hSide :
      Set.range iOld ∩ Set.range iB = Set.range (iOld.comp fOld) :=
    freeAmalgam_side_intersection hfree
  by_cases hSame : SameCopy cOld b₀
  · right
    refine ⟨iOld.comp fOld, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      have hxSide : x ∈ Set.range iOld ∩ Set.range iB := by
        constructor
        · rcases hx.1 with ⟨b, hb⟩
          exact ⟨cOld b, hb⟩
        · exact hx.2
      rw [hSide] at hxSide
      exact hxSide
    · intro x hx
      have hxSide : x ∈ Set.range iOld ∩ Set.range iB := by
        rw [hSide]
        exact hx
      rcases hx with ⟨a, ha⟩
      have hOldMem : fOld a ∈ copyCarrier cOld := by
        rw [hSame]
        exact hf₀ a
      rcases hOldMem with ⟨b, hb⟩
      constructor
      · refine ⟨b, ?_⟩
        change iOld (cOld b) = x
        calc
          iOld (cOld b) = iOld (fOld a) := congrArg iOld hb.symm
          _ = x := ha
      · exact hxSide.2
  · rcases hInter cOld b₀ hSame with hSmall | ⟨d, hd⟩
    · left
      intro x hx y hy
      rcases hx.1 with ⟨bx, hbx⟩
      rcases hy.1 with ⟨by, hby⟩
      have hxSide : x ∈ Set.range iOld ∩ Set.range iB :=
        ⟨⟨cOld bx, hbx⟩, hx.2⟩
      have hySide : y ∈ Set.range iOld ∩ Set.range iB :=
        ⟨⟨cOld by, hby⟩, hy.2⟩
      rw [hSide] at hxSide hySide
      rcases hxSide with ⟨ax, hax⟩
      rcases hySide with ⟨ay, hay⟩
      have hox : cOld bx = fOld ax := by
        apply iOld.injective
        exact hbx.trans hax.symm
      have hoy : cOld by = fOld ay := by
        apply iOld.injective
        exact hby.trans hay.symm
      have hold : cOld bx = cOld by := hSmall
        ⟨⟨bx, rfl⟩, by rw [hox]; exact hf₀ ax⟩
        ⟨⟨by, rfl⟩, by rw [hoy]; exact hf₀ ay⟩
      calc
        x = iOld (cOld bx) := hbx.symm
        _ = iOld (cOld by) := congrArg iOld hold
        _ = y := hby
    · have hOldLinear : ALinear A Old :=
        aLinear_of_base_and_controlled hBase hCover hInter
      by_cases hSameA : SameCopy d fOld
      · right
        refine ⟨iOld.comp fOld, ?_⟩
        apply Set.Subset.antisymm
        · intro x hx
          have hxSide : x ∈ Set.range iOld ∩ Set.range iB := by
            constructor
            · rcases hx.1 with ⟨b, hb⟩
              exact ⟨cOld b, hb⟩
            · exact hx.2
          rw [hSide] at hxSide
          exact hxSide
        · intro x hx
          have hxSide : x ∈ Set.range iOld ∩ Set.range iB := by
            rw [hSide]
            exact hx
          rcases hx with ⟨a, ha⟩
          have hfaD : fOld a ∈ copyCarrier d := by
            rw [hSameA]
            exact ⟨a, rfl⟩
          have hfaBoth : fOld a ∈ copyCarrier cOld ∩ copyCarrier b₀ := by
            rw [hd]
            exact hfaD
          rcases hfaBoth.1 with ⟨b, hb⟩
          constructor
          · refine ⟨b, ?_⟩
            change iOld (cOld b) = x
            calc
              iOld (cOld b) = iOld (fOld a) := congrArg iOld hb
              _ = x := ha
          · exact hxSide.2
      · left
        have hSmallA := hOldLinear d fOld hSameA
        intro x hx y hy
        rcases hx.1 with ⟨bx, hbx⟩
        rcases hy.1 with ⟨by, hby⟩
        have hxSide : x ∈ Set.range iOld ∩ Set.range iB :=
          ⟨⟨cOld bx, hbx⟩, hx.2⟩
        have hySide : y ∈ Set.range iOld ∩ Set.range iB :=
          ⟨⟨cOld by, hby⟩, hy.2⟩
        rw [hSide] at hxSide hySide
        rcases hxSide with ⟨ax, hax⟩
        rcases hySide with ⟨ay, hay⟩
        have hox : cOld bx = fOld ax := by
          apply iOld.injective
          exact hbx.trans hax.symm
        have hoy : cOld by = fOld ay := by
          apply iOld.injective
          exact hby.trans hay.symm
        have hdx : cOld bx ∈ copyCarrier d := by
          rw [← hd]
          exact ⟨⟨bx, rfl⟩, by rw [hox]; exact hf₀ ax⟩
        have hdy : cOld by ∈ copyCarrier d := by
          rw [← hd]
          exact ⟨⟨by, rfl⟩, by rw [hoy]; exact hf₀ ay⟩
        have hold : cOld bx = cOld by := hSmallA
          ⟨hdx, by rw [hox]; exact ⟨ax, rfl⟩⟩
          ⟨hdy, by rw [hoy]; exact ⟨ay, rfl⟩⟩
        calc
          x = iOld (cOld bx) := hbx.symm
          _ = iOld (cOld by) := congrArg iOld hold
          _ = y := hby

/-- In a singleton free gluing, every old-copy/fresh-side
intersection is automatically subsingleton. -/
theorem crossSubsingleton_gluePoint
    {B : RelStructure L V} {Old : RelStructure L W}
    {X : Type v} {Whole : RelStructure L X}
    {D : RelStructure L PUnit}
    (fOld : Embedding D Old) (fB : Embedding D B)
    (iOld : Embedding Old Whole) (iB : Embedding B Whole)
    (hfree : IsFreeAmalgam fOld fB iOld iB)
    (cOld : Embedding B Old) :
    (copyCarrier (iOld.comp cOld) ∩ copyCarrier iB).Subsingleton := by
  have hSide :
      Set.range iOld ∩ Set.range iB = Set.range (iOld.comp fOld) :=
    freeAmalgam_side_intersection hfree
  intro x hx y hy
  have hxSide : x ∈ Set.range iOld ∩ Set.range iB := by
    constructor
    · rcases hx.1 with ⟨b, hb⟩
      exact ⟨cOld b, hb⟩
    · exact hx.2
  have hySide : y ∈ Set.range iOld ∩ Set.range iB := by
    constructor
    · rcases hy.1 with ⟨b, hb⟩
      exact ⟨cOld b, hb⟩
    · exact hy.2
  rw [hSide] at hxSide hySide
  rcases hxSide with ⟨dx, hdx⟩
  rcases hySide with ⟨dy, hdy⟩
  have hxyD : dx = dy := Subsingleton.elim dx dy
  calc
    x = (iOld.comp fOld) dx := hdx.symm
    _ = (iOld.comp fOld) dy := congrArg (iOld.comp fOld) hxyD
    _ = y := hdy

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

/-- Pairwise `B`-copy intersections in an `A`-supported tree
amalgam are empty/singleton-sized or exactly an ambient `A`-copy. -/
theorem ASupportedTreeAmalgam.bIntersectionsControlled
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    [Finite V]
    (hA : A.Irreducible) (hB : B.Irreducible)
    (hBase : ALinear A B)
    (hT : ASupportedTreeAmalgam A B W T) :
    BIntersectionsControlled A B T := by
  classical
  induction hT with
  | copy h =>
      intro b₁ b₂ hne
      let j : Embedding B _ := h.toEmbedding
      have hfull (b : Embedding B _) : SameCopy b j := by
        apply sameCopy_of_range_subset b j
        intro x
        refine ⟨h.toEquiv.symm (b x), ?_⟩
        change b x = h.toEquiv (h.toEquiv.symm (b x))
        simp
      exact (hne ((hfull b₁).trans (hfull b₂).symm)).elim
  | glueA h₀ f₀ fB i₀ iB hfree ih =>
      intro b₁ b₂ hne
      have hCover₀ : ACopiesCoveredByB A B _ :=
        h₀.aCopiesCoveredByB hA
      rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₁ with
        ⟨c₁, hc₁⟩ | ⟨q₁, hq₁⟩
      · rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₂ with
          ⟨c₂, hc₂⟩ | ⟨q₂, hq₂⟩
        · have hneOld :
              ¬ SameCopy (i₀.comp c₁) (i₀.comp c₂) := by
            intro h
            exact hne (hc₁.trans (h.trans hc₂.symm))
          have hres := controlledIntersection_comp ih i₀ c₁ c₂ hneOld
          simpa only [hc₁, hc₂] using hres
        · have hq₂full : SameCopy (iB.comp q₂) iB := by
            apply sameCopy_of_range_subset (iB.comp q₂) iB
            intro x
            exact ⟨q₂ x, rfl⟩
          have hb₂R : SameCopy b₂ iB := hq₂.trans hq₂full
          have hres :=
            crossControlled_glueA hBase hCover₀ ih
              f₀ fB i₀ iB hfree c₁
          simpa only [hc₁, hb₂R] using hres
      · have hq₁full : SameCopy (iB.comp q₁) iB := by
          apply sameCopy_of_range_subset (iB.comp q₁) iB
          intro x
          exact ⟨q₁ x, rfl⟩
        have hb₁R : SameCopy b₁ iB := hq₁.trans hq₁full
        rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₂ with
          ⟨c₂, hc₂⟩ | ⟨q₂, hq₂⟩
        · have hres :=
            crossControlled_glueA hBase hCover₀ ih
              f₀ fB i₀ iB hfree c₂
          rcases hres with hs | ⟨a, ha⟩
          · left
            simpa only [hb₁R, hc₂, Set.inter_comm] using hs
          · right
            refine ⟨a, ?_⟩
            simpa only [hb₁R, hc₂, Set.inter_comm] using ha
        · have hq₂full : SameCopy (iB.comp q₂) iB := by
            apply sameCopy_of_range_subset (iB.comp q₂) iB
            intro x
            exact ⟨q₂ x, rfl⟩
          have hb₂R : SameCopy b₂ iB := hq₂.trans hq₂full
          exact (hne (hb₁R.trans hb₂R.symm)).elim
  | gluePoint h₀ f₀ fB support₀ supportB i₀ iB hfree ih =>
      intro b₁ b₂ hne
      rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₁ with
        ⟨c₁, hc₁⟩ | ⟨q₁, hq₁⟩
      · rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₂ with
          ⟨c₂, hc₂⟩ | ⟨q₂, hq₂⟩
        · have hneOld :
              ¬ SameCopy (i₀.comp c₁) (i₀.comp c₂) := by
            intro h
            exact hne (hc₁.trans (h.trans hc₂.symm))
          have hres := controlledIntersection_comp ih i₀ c₁ c₂ hneOld
          simpa only [hc₁, hc₂] using hres
        · have hq₂full : SameCopy (iB.comp q₂) iB := by
            apply sameCopy_of_range_subset (iB.comp q₂) iB
            intro x
            exact ⟨q₂ x, rfl⟩
          have hb₂R : SameCopy b₂ iB := hq₂.trans hq₂full
          left
          have hs :=
            crossSubsingleton_gluePoint f₀ fB i₀ iB hfree c₁
          simpa only [hc₁, hb₂R] using hs
      · have hq₁full : SameCopy (iB.comp q₁) iB := by
          apply sameCopy_of_range_subset (iB.comp q₁) iB
          intro x
          exact ⟨q₁ x, rfl⟩
        have hb₁R : SameCopy b₁ iB := hq₁.trans hq₁full
        rcases irreducibleCopy_side_of_freeAmalgam hfree hB b₂ with
          ⟨c₂, hc₂⟩ | ⟨q₂, hq₂⟩
        · left
          have hs :=
            crossSubsingleton_gluePoint f₀ fB i₀ iB hfree c₂
          simpa only [hb₁R, hc₂, Set.inter_comm] using hs
        · have hq₂full : SameCopy (iB.comp q₂) iB := by
            apply sameCopy_of_range_subset (iB.comp q₂) iB
            intro x
            exact ⟨q₂ x, rfl⟩
          have hb₂R : SameCopy b₂ iB := hq₂.trans hq₂full
          exact (hne (hb₁R.trans hb₂R.symm)).elim

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
