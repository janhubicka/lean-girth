import Girth.Track1FreeAmalgamSupport
import Girth.Track1StrongOverlapGirthThree
import Girth.LinearityGirthTwo
import Girth.SupportGirthEmbeddingEquiv
import Mathlib.Tactic

/-!
# Track 1: girth >3 of an actual A-strong relational free amalgam

Uses the checked strongness of each constituent's image in a free
amalgam and the draft three-edge side-case lemma. Neither a cycle
rank nor a train/forest construction is involved.

This exact statement is the extra geometric endpoint needed by the
triangle-free restriction of the canonical c_A EHN class.

DRAFT: this new file and its imported Track1 modules are NOT
kernel-compiled or axiom-checked on this head.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA D E F C : Type v}

/-- An A-copy coming from the right that meets the common base twice
also has a genuine embedding into the left constituent. -/
theorem track1_rightCopy_reflect_left
    {A : RelStructure L UA}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hBaseR : AStrong A Right (copyCarrier fR))
    (hfree : IsFreeAmalgam fL fR iL iR)
    (aR : Embedding A Right)
    (hMeet : ¬(copyCarrier (iR.comp aR) ∩
      copyCarrier (iL.comp fL)).Subsingleton) :
    ∃ aL : Embedding A Left,
      SameCopy (iL.comp aL) (iR.comp aR) := by
  classical
  have hBaseSub : copyCarrier (iL.comp fL) ⊆ copyCarrier iL := by
    rintro z ⟨d, hd⟩
    exact ⟨fL d, hd⟩
  have hMeetLeft :
      ¬ (copyCarrier (iR.comp aR) ∩ copyCarrier iL).Subsingleton := by
    intro hs
    apply hMeet
    intro x hx y hy
    exact hs ⟨hx.1, hBaseSub hx.2⟩
      ⟨hy.1, hBaseSub hy.2⟩
  have hLeftStrong : AStrong A Whole (copyCarrier iL) :=
    freeAmalgam_left_aStrong hA hBaseR hfree
  have hSub : copyCarrier (iR.comp aR) ⊆ copyCarrier iL :=
    hLeftStrong (iR.comp aR) hMeetLeft
  have hFactor : ∀ x : UA, ∃ y : E,
      (iR.comp aR) x = iL y := by
    intro x
    obtain ⟨y, hy⟩ := hSub ⟨x, rfl⟩
    exact ⟨y, hy.symm⟩
  let aL : Embedding A Left :=
    (iR.comp aR).factorThroughRange iL hFactor
  have hMap (x : UA) : (iR.comp aR) x = iL (aL x) :=
    Classical.choose_spec (hFactor x)
  refine ⟨aL, ?_⟩
  change Set.range (iL.comp aL) = Set.range (iR.comp aR)
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨x, (hMap x).symm⟩
  · rintro z ⟨x, rfl⟩
    exact ⟨x, hMap x⟩

/-- The corresponding reflection from the left side into the right. -/
theorem track1_leftCopy_reflect_right
    {A : RelStructure L UA}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hfree : IsFreeAmalgam fL fR iL iR)
    (aL : Embedding A Left)
    (hMeet : ¬(copyCarrier (iL.comp aL) ∩
      copyCarrier (iL.comp fL)).Subsingleton) :
    ∃ aR : Embedding A Right,
      SameCopy (iR.comp aR) (iL.comp aL) := by
  classical
  have hCommonEq :
      copyCarrier (iL.comp fL) = copyCarrier (iR.comp fR) := by
    change Set.range (iL.comp fL) = Set.range (iR.comp fR)
    apply Set.Subset.antisymm
    · rintro z ⟨d, rfl⟩
      exact ⟨d, ((hfree.overlap (fL d) (fR d)).mpr
        ⟨d, rfl, rfl⟩).symm⟩
    · rintro z ⟨d, rfl⟩
      exact ⟨d, ((hfree.overlap (fL d) (fR d)).mpr
        ⟨d, rfl, rfl⟩)⟩
  have hBaseSub : copyCarrier (iR.comp fR) ⊆ copyCarrier iR := by
    rintro z ⟨d, hd⟩
    exact ⟨fR d, hd⟩
  have hMeetRight :
      ¬ (copyCarrier (iL.comp aL) ∩ copyCarrier iR).Subsingleton := by
    intro hs
    apply hMeet
    intro x hx y hy
    apply hs
    · exact ⟨hx.1, hBaseSub (by rw [← hCommonEq]; exact hx.2)⟩
    · exact ⟨hy.1, hBaseSub (by rw [← hCommonEq]; exact hy.2)⟩
  have hRightStrong : AStrong A Whole (copyCarrier iR) :=
    freeAmalgam_right_aStrong hA hBaseL hfree
  have hSub : copyCarrier (iL.comp aL) ⊆ copyCarrier iR :=
    hRightStrong (iL.comp aL) hMeetRight
  have hFactor : ∀ x : UA, ∃ y : F,
      (iL.comp aL) x = iR y := by
    intro x
    obtain ⟨y, hy⟩ := hSub ⟨x, rfl⟩
    exact ⟨y, hy.symm⟩
  let aR : Embedding A Right :=
    (iL.comp aL).factorThroughRange iR hFactor
  have hMap (x : UA) : (iL.comp aL) x = iR (aR x) :=
    Classical.choose_spec (hFactor x)
  refine ⟨aR, ?_⟩
  change Set.range (iR.comp aR) = Set.range (iL.comp aL)
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨x, (hMap x).symm⟩
  · rintro z ⟨x, rfl⟩
    exact ⟨x, hMap x⟩

/-- The complete A-support of the free amalgam retains
girth greater than three under the two constituent bounds,
A-linearity and A-strong overlap. -/
theorem track1_girthGT_three_freeAmalgam_of_aStrong
    {A : RelStructure L UA}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hLinearL : ALinear A Left)
    (hLinearR : ALinear A Right)
    (hBaseL : AStrong A Left (copyCarrier fL))
    (hBaseR : AStrong A Right (copyCarrier fR))
    (hGirthL : GirthGT (supportCopies A Left) 3)
    (hGirthR : GirthGT (supportCopies A Right) 3)
    (hfree : IsFreeAmalgam fL fR iL iR) :
    GirthGT (supportCopies A Whole) 3 := by
  classical
  let HL := mappedSupportCopies A Left Whole iL
  let HR := mappedSupportCopies A Right Whole iR
  let S := copyCarrier (iL.comp fL)
  have hSupportUnion : supportCopies A Whole = HL ∪ HR :=
    track1_supportCopies_freeAmalgam_union hA hfree
  have hL : GirthGT HL 3 :=
    girthGT_mappedSupportCopies A Left Whole iL hGirthL
  have hR : GirthGT HR 3 :=
    girthGT_mappedSupportCopies A Right Whole iR hGirthR
  have hLinearWhole : ALinear A Whole :=
    aLinear_of_freeAmalgam hA hLinearL hLinearR hBaseL hBaseR hfree
  have hUnionTwo : GirthGT (HL ∪ HR) 2 := by
    rw [← hSupportUnion]
    exact girthGT_two_of_aLinear A Whole hLinearWhole
  have hCross : ∀ ⦃e f : Set C⦄, e ∈ HL → f ∈ HR →
      e ∩ f ⊆ S := by
    intro e f he hf
    obtain ⟨aL, rfl⟩ := he
    obtain ⟨aR, rfl⟩ := hf
    exact track1_crossSupport_intersection_common hfree aL aR
  have hReflectR : ∀ ⦃e : Set C⦄, e ∈ HR →
      ¬ (e ∩ S).Subsingleton → e ∈ HL := by
    intro e he hbig
    obtain ⟨aR, rfl⟩ := he
    obtain ⟨aL, hsame⟩ :=
      track1_rightCopy_reflect_left hA hBaseR hfree aR hbig
    exact ⟨aL, hsame.symm⟩
  have hReflectL : ∀ ⦃e : Set C⦄, e ∈ HL →
      ¬ (e ∩ S).Subsingleton → e ∈ HR := by
    intro e he hbig
    obtain ⟨aL, rfl⟩ := he
    obtain ⟨aR, hsame⟩ :=
      track1_leftCopy_reflect_right hA hBaseL hfree aL hbig
    exact ⟨aR, hsame.symm⟩
  have hWhole : GirthGT (HL ∪ HR) 3 :=
    girthGT_three_union_of_strong_overlap
      HL HR S hL hR hUnionTwo hCross hReflectR hReflectL
  rw [hSupportUnion]
  exact hWhole

#print axioms StructuralRamsey.Girth.track1_rightCopy_reflect_left
#print axioms StructuralRamsey.Girth.track1_leftCopy_reflect_right
#print axioms StructuralRamsey.Girth.track1_girthGT_three_freeAmalgam_of_aStrong

end StructuralRamsey.Girth
