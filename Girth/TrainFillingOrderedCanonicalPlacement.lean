import Girth.Support

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {U V W X : Type v}
variable {A₀ : RelStructure L U} [LinearOrder U]
variable {B : RelStructure L.withOrder V} {D : RelStructure L.withOrder W}

/-- Use the unique ordered old-edge embedding to place the entire filling
template. This uses only the order comparisons on that edge. -/
noncomputable def orderedFillingPlacement (enumerate : X ≃ U)
    (e : {s : Set W // s ∈ supportCopies A₀.ordered D}) : X ↪ W where
  toFun := fun x => (Classical.choose e.2) (enumerate x)
  inj' := (Classical.choose e.2).injective.comp enumerate.injective

theorem orderedFillingPlacement_range (enumerate : X ≃ U)
    (e : {s : Set W // s ∈ supportCopies A₀.ordered D}) :
    Set.range (orderedFillingPlacement enumerate e) = e.1 := by
  have hEdge : e.1 = copyCarrier (Classical.choose e.2) :=
    Classical.choose_spec e.2
  refine Eq.trans ?_ hEdge.symm
  ext w
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨enumerate x, hx⟩
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := enumerate.surjective a
    exact ⟨x, ha⟩

/-- Filling commutes pointwise with an actual ordered selected embedding.
The target order may be partial outside the old edges. -/
theorem orderedFillingPlacement_comp [Finite U] (enumerate : X ≃ U)
    (source : Embedding A₀.ordered B) (selected : Embedding B D)
    (e : {s : Set W // s ∈ supportCopies A₀.ordered D})
    (hEdge : e.1 = copyCarrier (selected.comp source)) (x : X) :
    orderedFillingPlacement enumerate e x = selected (source (enumerate x)) := by
  have hChosen : e.1 = copyCarrier (Classical.choose e.2) :=
    Classical.choose_spec e.2
  have hSame : SameCopy (Classical.choose e.2) (selected.comp source) :=
    hChosen.symm.trans hEdge
  have hEq := ordered_embedding_eq_of_sameCopy _ _ hSame
  change (Classical.choose e.2) (enumerate x) = selected (source (enumerate x))
  exact congrArg (fun f : Embedding A₀.ordered D => f (enumerate x)) hEq

end StructuralRamsey.Girth
