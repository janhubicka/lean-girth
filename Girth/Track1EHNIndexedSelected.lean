import Girth.Track1TriangleFreeSelectedFamily
import Girth.Track1OrderedPhysicalOwners

/-!
# Track 1: faithfully index the ACTUAL fresh-order selected EHN B images

The triangle-free EHN theorem returns a SET of full B embeddings,
with a specified Ramsey arrow on that very set. The partite and
owner-splitting libraries use indexed families.

Use the subtype of genuine selected embeddings as the index type,
not an arbitrary surjection or a copy of the image-carrier family.
The index map is injective, and its strongness, controlled
intersections, strict monotonicity and selected Ramsey arrow follow
literally from the old EHN witness. No duplicate physical copies
are introduced for finite globally ordered B.

STAGED DRAFT: no exact-head kernel certification.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB V : Type v}

/-- The honest index type of a selected set of target embeddings. -/
abbrev Track1SelectedIndex
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D)) :=
  {b : Embedding B D // b ∈ family}

/-- The literal selected embedding map is one-to-one; no choice of
representatives is required. -/
def track1_selectedEmbedding
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D)) :
    Track1SelectedIndex family → Embedding B D :=
  Subtype.val

theorem track1_selectedEmbedding_injective
    {B : RelStructure L VB} {D : RelStructure L V}
    (family : Set (Embedding B D)) :
    Function.Injective (track1_selectedEmbedding family) := by
  intro i j h
  exact Subtype.ext h

/-- Every property needed by the selected local witness survives
the honest subtype indexing, including the RAMSEY arrow. -/
theorem track1_selectedIndexedProperties
    (A : RelStructure L UA)
    {B : RelStructure L VB} {D : RelStructure L V}
    [LinearOrder VB] [LinearOrder V]
    (family : Set (Embedding B D))
    (hMono : ∀ b : Embedding B D,
      b ∈ family → StrictMono b)
    (hStrong : ∀ b : Embedding B D,
      b ∈ family → AStrong A D (copyCarrier b))
    (hControlled : ∀ b c : Embedding B D,
      b ∈ family → c ∈ family →
      ¬ SameCopy b c →
        (copyCarrier b ∩ copyCarrier c).Subsingleton ∨
          ∃ a : Embedding A D,
            copyCarrier b ∩ copyCarrier c = copyCarrier a)
    {κ : Type w}
    (hArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂)) :
    let selected := track1_selectedEmbedding family
    Function.Injective selected ∧
      (∀ c : Track1SelectedIndex family, StrictMono (selected c)) ∧
      (∀ c : Track1SelectedIndex family,
        AStrong A D (copyCarrier (selected c))) ∧
      (∀ i j : Track1SelectedIndex family,
        ¬ SameCopy (selected i) (selected j) →
          (copyCarrier (selected i) ∩ copyCarrier (selected j)).Subsingleton ∨
            ∃ a : Embedding A D,
              copyCarrier (selected i) ∩ copyCarrier (selected j) =
                copyCarrier a) ∧
      (∀ χ : Embedding A D → κ,
        ∃ c : Track1SelectedIndex family,
          ∀ a₁ a₂ : Embedding A B,
            χ ((selected c).comp a₁) =
              χ ((selected c).comp a₂)) := by
  classical
  dsimp
  refine ⟨track1_selectedEmbedding_injective family, ?_, ?_, ?_, ?_⟩
  · intro c
    exact hMono c.1 c.2
  · intro c
    exact hStrong c.1 c.2
  · intro i j hne
    exact hControlled i.1 j.1 i.2 j.2 hne
  · intro χ
    obtain ⟨b, hb, hmono⟩ := hArrow χ
    exact ⟨⟨b, hb⟩, hmono⟩

#print axioms StructuralRamsey.Girth.track1_selectedEmbedding_injective
#print axioms StructuralRamsey.Girth.track1_selectedIndexedProperties

end StructuralRamsey.Girth
