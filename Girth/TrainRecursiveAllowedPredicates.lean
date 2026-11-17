import PartiteConstruction.Relational.Order

set_option autoImplicit false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The original unary symbols determine the allowed vertices on each cut.
The same formula can be evaluated in the Ramsey base. -/
def allowedByPredicates {X : Type v} {J : Type w}
    (C : RelStructure L.withOrder X) (symbols : J → Set L.Symbol)
    (j : J) : Set X :=
  {x | ∃ R ∈ symbols j, C.rel (.inl R) (fun _ => x)}

theorem allowedByPredicates_pullback
    {J : Type w} {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P} (b : Embedding B D)
    (symbols : J → Set L.Symbol) (j : J) :
    b ⁻¹' allowedByPredicates D symbols j = allowedByPredicates B symbols j := by
  ext x
  change (∃ R ∈ symbols j, D.rel (.inl R) (fun _ => b x)) ↔
    (∃ R ∈ symbols j, B.rel (.inl R) (fun _ => x))
  constructor
  · rintro ⟨R, hR, he⟩
    exact ⟨R, hR, (b.map_rel_iff (.inl R) (fun _ => x)).mp he⟩
  · rintro ⟨R, hR, he⟩
    exact ⟨R, hR, (b.map_rel_iff (.inl R) (fun _ => x)).mpr he⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
