import Girth.SupportedTreeConstruction
import PartiteConstruction.Iterated.MixedOverlapExactness

/-! # Free decomposition of an induced union

For the forest-to-tree-amalgam induction we repeatedly peel off one member.
The ambient induced structure is then a free amalgam of the peeled member and
the remaining union, provided every relation tuple is contained wholly in one
of the two sides.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {W : Type v}

/-- Inclusion between two induced substructures of the same relational
structure. -/
def induceEmbeddingOfSubset
    (R : RelStructure L W)
    {S T : Set W} (hST : S ⊆ T) :
    Embedding (R.induce S) (R.induce T) where
  toFun x := ⟨x.1, hST x.2⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro sym x
    rfl

/-- Every relation tuple in the induced union is wholly contained in one side. -/
def RelationsSplitOver
    (R : RelStructure L W) (S T : Set W) : Prop :=
  ∀ (sym : L.Symbol) (x : Fin (L.arity sym) → W),
    R.rel sym x →
    (∀ i, x i ∈ S ∪ T) →
      (∀ i, x i ∈ S) ∨ (∀ i, x i ∈ T)

/-- More flexible union decomposition with an arbitrary chosen overlap
structure.  It is enough that the two overlap embeddings identify exactly the
common vertices of the two sides. -/
theorem induceUnion_isFreeAmalgam_of_overlap
    {D : Type v} (R : RelStructure L W)
    (S T : Set W) (O : RelStructure L D)
    (fS : Embedding O (R.induce S))
    (fT : Embedding O (R.induce T))
    (hOverlap :
      ∀ a : ↥S, ∀ b : ↥T,
        a.1 = b.1 ↔
          ∃ d : D, a = fS d ∧ b = fT d)
    (hSplit : RelationsSplitOver R S T) :
    IsFreeAmalgam
      fS fT
      (induceEmbeddingOfSubset R Set.subset_union_left)
      (induceEmbeddingOfSubset R Set.subset_union_right) := by
  classical
  constructor
  · intro z
    rcases z.2 with hzS | hzT
    · exact Or.inl ⟨⟨z.1, hzS⟩, by apply Subtype.ext; rfl⟩
    · exact Or.inr ⟨⟨z.1, hzT⟩, by apply Subtype.ext; rfl⟩
  · intro a b
    change a.1 = b.1 ↔ ∃ d : D, a = fS d ∧ b = fT d
    exact hOverlap a b
  · intro sym z
    constructor
    · intro hz
      have hzR : R.rel sym (Subtype.val ∘ z) := hz
      have hzUnion : ∀ i, (Subtype.val ∘ z) i ∈ S ∪ T :=
        fun i => (z i).2
      rcases hSplit sym (Subtype.val ∘ z) hzR hzUnion with hS | hT
      · let x : Fin (L.arity sym) → ↥S :=
          fun i => ⟨(z i).1, hS i⟩
        refine Or.inl ⟨x, ?_, ?_⟩
        · exact hzR
        · funext i
          apply Subtype.ext
          rfl
      · let x : Fin (L.arity sym) → ↥T :=
          fun i => ⟨(z i).1, hT i⟩
        refine Or.inr ⟨x, ?_, ?_⟩
        · exact hzR
        · funext i
          apply Subtype.ext
          rfl
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact hx
      · exact hx


/-- Under relation splitting, the structure induced on a union is exactly the
free amalgam of the two induced sides over their intersection. -/
theorem induceUnion_isFreeAmalgam
    (R : RelStructure L W)
    (S T : Set W)
    (hSplit : RelationsSplitOver R S T) :
    IsFreeAmalgam
      (induceEmbeddingOfSubset R Set.inter_subset_left)
      (induceEmbeddingOfSubset R Set.inter_subset_right)
      (induceEmbeddingOfSubset R Set.subset_union_left)
      (induceEmbeddingOfSubset R Set.subset_union_right) := by
  classical
  constructor
  · intro z
    rcases z.2 with hzS | hzT
    · exact Or.inl ⟨⟨z.1, hzS⟩, by apply Subtype.ext; rfl⟩
    · exact Or.inr ⟨⟨z.1, hzT⟩, by apply Subtype.ext; rfl⟩
  · intro a b
    constructor
    · intro hab
      have hv : a.1 = b.1 :=
        congrArg Subtype.val hab
      let d : ↥(S ∩ T) :=
        ⟨a.1, a.2, by simpa [← hv] using b.2⟩
      refine ⟨d, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hv.symm
    · rintro ⟨d, rfl, rfl⟩
      rfl
  · intro sym z
    constructor
    · intro hz
      have hzR : R.rel sym (Subtype.val ∘ z) := hz
      have hzUnion : ∀ i, (Subtype.val ∘ z) i ∈ S ∪ T :=
        fun i => (z i).2
      rcases hSplit sym (Subtype.val ∘ z) hzR hzUnion with hS | hT
      · let x : Fin (L.arity sym) → ↥S :=
          fun i => ⟨(z i).1, hS i⟩
        refine Or.inl ⟨x, ?_, ?_⟩
        · exact hzR
        · funext i
          apply Subtype.ext
          rfl
      · let x : Fin (L.arity sym) → ↥T :=
          fun i => ⟨(z i).1, hT i⟩
        refine Or.inr ⟨x, ?_, ?_⟩
        · exact hzR
        · funext i
          apply Subtype.ext
          rfl
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact hx
      · exact hx


/-- When source and target free amalgams use the same overlap structure, exact
overlap reflection is automatic from injectivity of the two side embeddings. -/
noncomputable def StructuralRamsey.RelStructure.IsFreeAmalgam.liftEmbedding_sameOverlap
    {H E F C E₂ F₂ T : Type v}
    {D : RelStructure L H}
    {A₁ : RelStructure L E} {B₁ : RelStructure L F}
    {C₁ : RelStructure L C}
    {A₂ : RelStructure L E₂} {B₂ : RelStructure L F₂}
    {C₂ : RelStructure L T}
    {sA : Embedding D A₁} {sB : Embedding D B₁}
    {iA : Embedding A₁ C₁} {iB : Embedding B₁ C₁}
    {tA : Embedding D A₂} {tB : Embedding D B₂}
    {jA : Embedding A₂ C₂} {jB : Embedding B₂ C₂}
    (hSrc : IsFreeAmalgam sA sB iA iB)
    (hTgt : IsFreeAmalgam tA tB jA jB)
    (hA : Embedding A₁ A₂) (hB : Embedding B₁ B₂)
    (hcompatA : ∀ d, hA (sA d) = tA d)
    (hcompatB : ∀ d, hB (sB d) = tB d) :
    Embedding C₁ C₂ := by
  apply StructuralRamsey.RelStructure.IsFreeAmalgam.liftEmbedding
    hSrc hTgt (fun d => d) hA hB hcompatA hcompatB
  · intro a g hag
    refine ⟨g, ?_, rfl⟩
    apply hA.injective
    exact hag.trans (hcompatA g).symm
  · intro b g hbg
    refine ⟨g, ?_, rfl⟩
    apply hB.injective
    exact hbg.trans (hcompatB g).symm

end StructuralRamsey.Girth
