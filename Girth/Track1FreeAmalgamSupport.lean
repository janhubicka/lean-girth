import Girth.ElementaryClosureAmalgam
import Girth.Berge

/-!
# Track 1: exact support edges of a relational free amalgam

All support A-copies of an actual free amalgam come from its two
real constituents (by irreducibility), and contacts between
one left and one right support edge occur only in the
literal common domain. These are two of the input adapters for
the new strong-overlap girth>3 theorem.

DRAFT, NOT LEAN-CHECKED at this exact head.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA D E F C : Type v}

/-- There are no additional A-support edges crossing the private
sides of a true free amalgam of relational structures. -/
theorem track1_supportCopies_freeAmalgam_union
    {A : RelStructure L UA}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hA : A.Irreducible)
    (hfree : IsFreeAmalgam fL fR iL iR) :
    supportCopies A Whole =
      mappedSupportCopies A Left Whole iL ∪
      mappedSupportCopies A Right Whole iR := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    rcases irreducibleCopy_side_of_freeAmalgam hfree hA a with
      ⟨aL, haL⟩ | ⟨aR, haR⟩
    · exact Or.inl ⟨aL, haL⟩
    · exact Or.inr ⟨aR, haR⟩
  · rintro (⟨aL, rfl⟩ | ⟨aR, rfl⟩)
    · exact ⟨iL.comp aL, rfl⟩
    · exact ⟨iR.comp aR, rfl⟩

/-- A left and right embedded A-copy can meet only at vertices of
the actual common induced domain, not at private vertices. -/
theorem track1_crossSupport_intersection_common
    {A : RelStructure L UA}
    {Base : RelStructure L D}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {fL : Embedding Base Left} {fR : Embedding Base Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hfree : IsFreeAmalgam fL fR iL iR)
    (aL : Embedding A Left) (aR : Embedding A Right) :
    copyCarrier (iL.comp aL) ∩ copyCarrier (iR.comp aR) ⊆
      copyCarrier (iL.comp fL) := by
  intro z hz
  have hzL : z ∈ Set.range iL := by
    rcases hz.1 with ⟨a, ha⟩
    exact ⟨aL a, ha⟩
  have hzR : z ∈ Set.range iR := by
    rcases hz.2 with ⟨a, ha⟩
    exact ⟨aR a, ha⟩
  have hzBoth : z ∈ Set.range iL ∩ Set.range iR :=
    ⟨hzL, hzR⟩
  rw [freeAmalgam_side_intersection hfree] at hzBoth
  exact hzBoth

#print axioms StructuralRamsey.Girth.track1_supportCopies_freeAmalgam_union
#print axioms StructuralRamsey.Girth.track1_crossSupport_intersection_common

end StructuralRamsey.Girth
