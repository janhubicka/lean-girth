import Girth.TrainFillingLocalPrivateChoices

set_option autoImplicit false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {A V W X Y P I : Type v}

/-- Restricting a strong marked copy to one strong induced summand
preserves two-point strongness for the same physical edge type. -/
theorem aStrong_comp_of_aStrong
    (small : RelStructure L A) (B : RelStructure L V)
    (M : RelStructure L W) (N : RelStructure L X)
    (localCopy : Embedding B M) (marked : Embedding M N)
    (hLocal : AStrong small M (copyCarrier localCopy))
    (hMarked : AStrong small N (copyCarrier marked)) :
    AStrong small N (copyCarrier (marked.comp localCopy)) := by
  intro a hMeet
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hMeet
  have hSub : copyCarrier a ⊆ copyCarrier marked := by
    apply hMarked a
    intro hSmall
    obtain ⟨u, hu⟩ := hx.2
    obtain ⟨v, hv⟩ := hy.2
    exact hxy (hSmall ⟨hx.1, localCopy u, hu⟩ ⟨hy.1, localCopy v, hv⟩)
  have hFactor (u : A) : ∃ z : W, a u = marked z := by
    obtain ⟨z, hz⟩ := hSub ⟨u, rfl⟩
    exact ⟨z, hz.symm⟩
  let a' : Embedding small M := a.factorThroughRange marked hFactor
  have hApply (u : A) : a u = marked (a' u) := Classical.choose_spec (hFactor u)
  have hInto : copyCarrier a' ⊆ copyCarrier localCopy := by
    apply hLocal a'
    intro hSmall
    obtain ⟨a₁, ha₁⟩ := hx.1
    obtain ⟨a₂, ha₂⟩ := hy.1
    obtain ⟨b₁, hb₁⟩ := hx.2
    obtain ⟨b₂, hb₂⟩ := hy.2
    have h₁ : localCopy b₁ = a' a₁ :=
      marked.injective (hb₁.trans (ha₁.symm.trans (hApply a₁)))
    have h₂ : localCopy b₂ = a' a₂ :=
      marked.injective (hb₂.trans (ha₂.symm.trans (hApply a₂)))
    have hEq : a' a₁ = a' a₂ := hSmall
      ⟨⟨a₁, rfl⟩, ⟨b₁, h₁⟩⟩ ⟨⟨a₂, rfl⟩, ⟨b₂, h₂⟩⟩
    exact hxy (ha₁.symm.trans ((hApply a₁).trans
      ((congrArg marked hEq).trans ((hApply a₂).symm.trans ha₂))))
  rintro _ ⟨u, rfl⟩
  obtain ⟨z, hz⟩ := hInto ⟨u, rfl⟩
  exact ⟨z, (congrArg marked hz).trans (hApply u).symm⟩

/-- Each chosen marked W-copy supplies all original first-wagon maps
from its genuine induced summands, with local strongness and coverage. -/
noncomputable def privateChoicesOfMarkedSummands
    (small : RelStructure L A) (Target : RelStructure L V)
    (Completed : RelStructure L W) (R : RelStructure L X)
    (carrier : P → Set V)
    (summand : ∀ p : P, Embedding (Target.induce (carrier p)) Completed)
    (marked : I → Embedding Completed R)
    (hSummand : ∀ p, AStrong small Completed (copyCarrier (summand p)))
    (hMarked : ∀ i, AStrong small R (copyCarrier (marked i)))
    (hCover : ∀ p : P, ∀ x : {v : V // v ∈ carrier p},
      ∃ a : Embedding small (Target.induce (carrier p)), x ∈ copyCarrier a) :
    I → PrivateWagonInput V P X :=
  fun i => privateChoiceOfLocalCopies small Target R carrier
    (fun p => (marked i).comp (summand p))
    (fun p => aStrong_comp_of_aStrong small _ Completed R (summand p) (marked i)
      (hSummand p) (hMarked i)) hCover

end StructuralRamsey.Girth
