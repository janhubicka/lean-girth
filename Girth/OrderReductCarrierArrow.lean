import Girth.SupportedTreeOrderReduct

/-! # Transfer a colour on edge carriers through forgetting order -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {U V W : Type v}

private theorem copyCarrier_comp_image
    {A : RelStructure L U} {B : RelStructure L V} {C : RelStructure L W}
    (f : Embedding B C) (g : Embedding A B) :
    copyCarrier (f.comp g) = f '' copyCarrier g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨g y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- Every unordered A-carrier in the target must lift to an ordered A-copy
on the same carrier. Colouring the ordered embeddings by their unordered
carriers then gives a copy of the target whose unordered edges are
monochromatic. The witness need not carry a complete order. -/
theorem arrow_orderReduct_carriers
    {A : RelStructure L.withOrder U} {B : RelStructure L.withOrder V}
    {C : RelStructure L.withOrder W} {κ : Type*}
    (hArrow : StructuralRamsey.Arrow A B C κ)
    (hLift : supportCopies A.orderReduct B.orderReduct ⊆ supportCopies A B) :
    ∀ χ : supportCopies A.orderReduct C.orderReduct → κ,
      ∃ f : Embedding B.orderReduct C.orderReduct,
        ∀ g h : Embedding A.orderReduct B.orderReduct,
          χ ⟨copyCarrier (f.comp g), ⟨f.comp g, rfl⟩⟩ =
            χ ⟨copyCarrier (f.comp h), ⟨f.comp h, rfl⟩⟩ := by
  intro χ
  let colour (e : Embedding A C) : κ :=
    χ ⟨copyCarrier e, ⟨e.orderReduct, rfl⟩⟩
  obtain ⟨f, hf⟩ := hArrow colour
  refine ⟨f.orderReduct, fun g h => ?_⟩
  obtain ⟨g', hg⟩ := hLift (show copyCarrier g ∈ _ from ⟨g, rfl⟩)
  obtain ⟨h', hh⟩ := hLift (show copyCarrier h ∈ _ from ⟨h, rfl⟩)
  have compatible (k : Embedding A.orderReduct B.orderReduct)
      (k' : Embedding A B) (hk : copyCarrier k = copyCarrier k') :
      χ ⟨copyCarrier (f.orderReduct.comp k), ⟨f.orderReduct.comp k, rfl⟩⟩ =
        colour (f.comp k') := by
    apply congrArg χ
    apply Subtype.ext
    change copyCarrier (f.orderReduct.comp k) = copyCarrier (f.comp k')
    rw [copyCarrier_comp_image, copyCarrier_comp_image, hk]
    rfl
  exact (compatible g g' hg).trans ((hf g' h').trans (compatible h h' hh).symm)

end StructuralRamsey.Girth
