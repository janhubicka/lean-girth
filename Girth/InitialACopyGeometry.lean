import Girth.InitialDesignated
import Girth.Support

/-! # Geometry of A-copies in the initial picture

The initial partite picture is a disjoint union of B-copies.  Since A is
irreducible, every ambient A-copy lies wholly in one component and therefore
factors through the canonical embedding of that component.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P I : Type v}

/-- Every A-copy in the initial disjoint-union picture has one component
index. -/
theorem initialACopy_same_index
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) :
    ∃ i : I, ∀ u : UA, (a u).1 = i := by
  let T : Set (I × VB) := copyCarrier a
  have hT :
      ((StructuralRamsey.Partite.Initial.picture B β).toRelStructure.induce T).Irreducible :=
    hA.range_embedding a
  obtain ⟨i, hi⟩ :=
    StructuralRamsey.Partite.Induced.Initial.irreducible_same_index
      B β T hT
  refine ⟨i, ?_⟩
  intro u
  let z : T := ⟨a u, ⟨u, rfl⟩⟩
  exact hi z

/-- Equivalently, every ambient A-copy factors through one canonical B-component
of the initial picture. -/
theorem initialACopy_factors_component
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty I]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure) :
    ∃ (i : I) (aB : Embedding A B),
      a =
        (StructuralRamsey.Partite.Initial.copyEmbedding B β i).comp aB := by
  obtain ⟨i, hi⟩ := initialACopy_same_index A hA B β a
  let copy : Embedding B
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure :=
    StructuralRamsey.Partite.Initial.copyEmbedding B β i
  have hfactor :
      ∀ u : UA, ∃ b : VB, a u = copy b := by
    intro u
    refine ⟨(a u).2, ?_⟩
    apply Prod.ext
    · exact hi u
    · rfl
  let aB : Embedding A B :=
    a.factorThroughRange copy hfactor
  refine ⟨i, aB, ?_⟩
  apply Embedding.ext
  intro u
  exact Classical.choose_spec (hfactor u)


/-- Distinct canonical components of the initial picture are vertex-disjoint. -/
theorem initialComponent_inter_eq_empty
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    {i j : I} (hij : i ≠ j) :
    copyCarrier
        (StructuralRamsey.Partite.Initial.copyEmbedding B β i) ∩
      copyCarrier
        (StructuralRamsey.Partite.Initial.copyEmbedding B β j) = ∅ := by
  ext z
  constructor
  · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
    exfalso
    apply hij
    have hpair :
        (i, b) = (j, c) := hb.trans hc.symm
    exact congrArg Prod.fst hpair
  · intro hz
    simp at hz

/-- A nonempty ambient A-copy cannot be contained in two different initial
components. -/
theorem initialACopy_owner_unique
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (β : I → VB ↪ P)
    [Nonempty UA]
    (a : Embedding A
      (StructuralRamsey.Partite.Initial.picture B β).toRelStructure)
    {i j : I}
    (hi :
      copyCarrier a ⊆
        copyCarrier
          (StructuralRamsey.Partite.Initial.copyEmbedding B β i))
    (hj :
      copyCarrier a ⊆
        copyCarrier
          (StructuralRamsey.Partite.Initial.copyEmbedding B β j)) :
    i = j := by
  by_contra hij
  let u : UA := Classical.choice (inferInstance : Nonempty UA)
  have hz :
      a u ∈
        copyCarrier
            (StructuralRamsey.Partite.Initial.copyEmbedding B β i) ∩
          copyCarrier
            (StructuralRamsey.Partite.Initial.copyEmbedding B β j) :=
    ⟨hi ⟨u, rfl⟩, hj ⟨u, rfl⟩⟩
  rw [initialComponent_inter_eq_empty B β hij] at hz
  simpa using hz

end StructuralRamsey.Girth
