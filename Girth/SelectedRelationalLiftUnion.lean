import PartiteConstruction.Relational.Basic
import Mathlib.Logic.Embedding.Basic

namespace StructuralRamsey.Girth

universe u v

open StructuralRamsey.RelStructure

variable {L : RelLanguage.{u}} {U V W I : Type v}

/-- The union of the relations carried by the selected lifted copies. -/
def selectedRelationalLiftUnion (B : RelStructure L U) (lift : I → U ↪ W) :
    RelStructure L W where
  rel R t := ∃ i : I, ∃ s : Fin (L.arity R) → U,
    B.rel R s ∧ (lift i : U → W) ∘ s = t

/-- If the lifts project to original induced copies in one structure,
each lift is also induced in the union of the lifted relations. -/
def selectedRelationalLiftUnionEmbedding
    {B : RelStructure L U} {D : RelStructure L V}
    (original : I → Embedding B D) (lift : I → U ↪ W)
    (project : W → V) (hProject : ∀ i x, project (lift i x) = original i x)
    (i : I) : Embedding B (selectedRelationalLiftUnion B lift) where
  toFun := lift i
  injective := (lift i).injective
  map_rel_iff := by
    intro R s
    constructor
    · rintro ⟨j, t, hRel, hEq⟩
      apply ((original i).map_rel_iff R s).mp
      have hProjected : ((original j : U → V) ∘ t) = (original i : U → V) ∘ s := by
        funext k
        exact (hProject j (t k)).symm.trans
          ((congrArg project (congrFun hEq k)).trans (hProject i (s k)))
      rw [← hProjected]
      exact ((original j).map_rel_iff R t).mpr hRel
    · intro hRel
      exact ⟨i, s, hRel, rfl⟩

/-- A copy of a source with a relation tuple listing all its vertices
lies inside a single lifted copy. -/
theorem selectedRelationalLiftUnion_fullTuple_covered
    {A : RelStructure L U} {B : RelStructure L V} (lift : I → V ↪ W)
    (R : L.Symbol) (t : Fin (L.arity R) → U) (hRel : A.rel R t)
    (hFull : Function.Surjective t)
    (a : Embedding A (selectedRelationalLiftUnion B lift)) :
    ∃ i : I, Set.range a ⊆ Set.range (lift i) := by
  obtain ⟨i, s, _, hEq⟩ := (a.map_rel_iff R t).mpr hRel
  refine ⟨i, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, rfl⟩ := hFull x
  exact ⟨s k, congrFun hEq k⟩

end StructuralRamsey.Girth
