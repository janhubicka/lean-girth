import Girth.Berge
import PartiteConstruction.Iterated.LocalTreeLike

/-! # A-supported tree amalgams

This is the recursive gluing object from the girth manuscript.  Each step adds
one fresh copy of `B`, either over a whole copy of `A` or over one vertex
which lies in an `A`-copy on each side.

The first bridge theorem shows that every such object is also a generic tree
amalgam in the reusable partite-construction library.  The converse is false
and the extra restriction is precisely what carries the girth information.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W X : Type v}

/-- Tree amalgam of copies of `B` using only the two overlap types allowed
in the main girth theorem. -/
inductive ASupportedTreeAmalgam
    (A : RelStructure L U) (B : RelStructure L V) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W}
      (h : Iso B T) :
      ASupportedTreeAmalgam A B W T
  | glueA
      {W₀ W : Type v}
      {T₀ : RelStructure L W₀} {T : RelStructure L W}
      (h₀ : ASupportedTreeAmalgam A B W₀ T₀)
      (f₀ : Embedding A T₀) (fB : Embedding A B)
      (i₀ : Embedding T₀ T) (iB : Embedding B T)
      (hfree : IsFreeAmalgam f₀ fB i₀ iB) :
      ASupportedTreeAmalgam A B W T
  | gluePoint
      {W₀ W : Type v}
      {T₀ : RelStructure L W₀} {T : RelStructure L W}
      {D : RelStructure L PUnit}
      (h₀ : ASupportedTreeAmalgam A B W₀ T₀)
      (f₀ : Embedding D T₀) (fB : Embedding D B)
      (support₀ : ∃ α : Embedding A T₀, ∀ d, ∃ a, f₀ d = α a)
      (supportB : ∃ α : Embedding A B, ∀ d, ∃ a, fB d = α a)
      (i₀ : Embedding T₀ T) (iB : Embedding B T)
      (hfree : IsFreeAmalgam f₀ fB i₀ iB) :
      ASupportedTreeAmalgam A B W T

namespace ASupportedTreeAmalgam

/-- Forgetting the restricted overlap information gives the generic
`TreeAmalgam` used by the partite-construction formalization. -/
theorem toTreeAmalgam
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hA : A.Irreducible)
    (hT : ASupportedTreeAmalgam A B W T) :
    TreeAmalgam B W T := by
  induction hT with
  | copy h =>
      exact TreeAmalgam.copy h
  | glueA h₀ f₀ fB i₀ iB hfree ih =>
      refine TreeAmalgam.glue ih (TreeAmalgam.copy (Iso.refl B))
        f₀ fB ?_ ?_ i₀ iB hfree
      · exact Embedding.containedInIrreducible_of_range_subset
          hA f₀ f₀ (fun a => ⟨a, rfl⟩)
      · exact Embedding.containedInIrreducible_of_range_subset
          hA fB fB (fun a => ⟨a, rfl⟩)
  | gluePoint h₀ f₀ fB support₀ supportB i₀ iB hfree ih =>
      rcases support₀ with ⟨α₀, hα₀⟩
      rcases supportB with ⟨αB, hαB⟩
      refine TreeAmalgam.glue ih (TreeAmalgam.copy (Iso.refl B))
        f₀ fB ?_ ?_ i₀ iB hfree
      · exact Embedding.containedInIrreducible_of_range_subset hA α₀ f₀ hα₀
      · exact Embedding.containedInIrreducible_of_range_subset hA αB fB hαB

/-- Every irreducible substructure of an `A`-supported tree amalgam lies
inside a constituent copy of `B`. -/
theorem irreducible_contained_in_copy
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W} {D : RelStructure L X}
    (hA : A.Irreducible)
    (hT : ASupportedTreeAmalgam A B W T)
    (hD : D.Irreducible) (e : Embedding D T) :
    ∃ j : Embedding B T, ∀ d : X, ∃ b : V, e d = j b := by
  exact TreeAmalgam.irreducible_contained_in_copy
    (toTreeAmalgam hA hT) hD e

/-- In particular every ambient copy of `A` lies in a constituent
`B`-copy. -/
theorem aCopy_contained_in_copy
    {A : RelStructure L U} {B : RelStructure L V}
    {T : RelStructure L W}
    (hA : A.Irreducible)
    (hT : ASupportedTreeAmalgam A B W T)
    (e : Embedding A T) :
    ∃ j : Embedding B T, ∀ a : U, ∃ b : V, e a = j b := by
  exact irreducible_contained_in_copy hA hT hA e

end ASupportedTreeAmalgam

end StructuralRamsey.Girth
