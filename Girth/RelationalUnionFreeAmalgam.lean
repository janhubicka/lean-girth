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
    exact congrArg (fun z : ↥T => z.1) h
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
      (induceEmbeddingOfSubset R
        (S := S) (T := S ∪ T) Set.subset_union_left)
      (induceEmbeddingOfSubset R
        (S := T) (T := S ∪ T) Set.subset_union_right) := by
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
        congrArg (fun z : ↥(S ∪ T) => z.1) hab
      exact (hOverlap a b).mp hv
    · intro h
      have hv : a.1 = b.1 := (hOverlap a b).mpr h
      apply Subtype.ext
      exact hv
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
      (induceEmbeddingOfSubset R
        (S := S ∩ T) (T := S) Set.inter_subset_left)
      (induceEmbeddingOfSubset R
        (S := S ∩ T) (T := T) Set.inter_subset_right)
      (induceEmbeddingOfSubset R
        (S := S) (T := S ∪ T) Set.subset_union_left)
      (induceEmbeddingOfSubset R
        (S := T) (T := S ∪ T) Set.subset_union_right) := by
  apply induceUnion_isFreeAmalgam_of_overlap
    R S T (R.induce (S ∩ T))
    (induceEmbeddingOfSubset R
      (S := S ∩ T) (T := S) Set.inter_subset_left)
    (induceEmbeddingOfSubset R
      (S := S ∩ T) (T := T) Set.inter_subset_right)
  · intro a b
    constructor
    · intro hab
      let d : ↥(S ∩ T) := ⟨a.1, a.2, by simpa [hab] using b.2⟩
      refine ⟨d, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hab.symm
    · rintro ⟨d, ha, hb⟩
      have haVal := congrArg Subtype.val ha
      have hbVal := congrArg Subtype.val hb
      exact haVal.trans hbVal.symm
  · exact hSplit


/-- When source and target free amalgams use the same overlap structure, exact
overlap reflection is automatic from injectivity of the two side embeddings. -/
noncomputable def freeAmalgam_liftEmbedding_sameOverlap
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

/-- Canonical inclusion of an induced substructure into its ambient structure. -/
def induceToAmbient
    (R : RelStructure L W) (S : Set W) :
    Embedding (R.induce S) R where
  toFun x := x.1
  injective := by
    intro x y h
    exact Subtype.ext h
  map_rel_iff := by
    intro sym x
    rfl

/-- Embed the left side into the structure induced on the union of two image
ranges. -/
def leftToInducedImageUnion
    {A : RelStructure L W} {B : RelStructure L V}
    {X : Type v} {R : RelStructure L X}
    (iA : Embedding A R) (iB : Embedding B R) :
    Embedding A (R.induce (Set.range iA ∪ Set.range iB)) where
  toFun a := ⟨iA a, Or.inl ⟨a, rfl⟩⟩
  injective := by
    intro x y h
    apply iA.injective
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro sym x
    change R.rel sym (iA.toFun ∘ x) ↔ A.rel sym x
    exact iA.map_rel_iff sym x

/-- Embed the right side into the structure induced on the union of two image
ranges. -/
def rightToInducedImageUnion
    {A : RelStructure L W} {B : RelStructure L V}
    {X : Type v} {R : RelStructure L X}
    (iA : Embedding A R) (iB : Embedding B R) :
    Embedding B (R.induce (Set.range iA ∪ Set.range iB)) where
  toFun b := ⟨iB b, Or.inr ⟨b, rfl⟩⟩
  injective := by
    intro x y h
    apply iB.injective
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro sym x
    change R.rel sym (iB.toFun ∘ x) ↔ B.rel sym x
    exact iB.map_rel_iff sym x

/-- Disjoint side images with relation splitting form a free amalgam over any
empty common structure, after restricting the ambient structure to the union
of the two images. -/
theorem inducedImageUnion_isFreeAmalgam_of_disjoint
    {D : RelStructure L PEmpty}
    {A : RelStructure L W} {B : RelStructure L V}
    {X : Type v} {R : RelStructure L X}
    (fA : Embedding D A) (fB : Embedding D B)
    (iA : Embedding A R) (iB : Embedding B R)
    (hDisj : Disjoint (Set.range iA) (Set.range iB))
    (hSplit : RelationsSplitBetweenImages iA iB) :
    IsFreeAmalgam
      fA fB
      (leftToInducedImageUnion iA iB)
      (rightToInducedImageUnion iA iB) := by
  classical
  constructor
  · intro z
    rcases z.2 with hzA | hzB
    · rcases hzA with ⟨a, ha⟩
      exact Or.inl ⟨a, by apply Subtype.ext; exact ha.symm⟩
    · rcases hzB with ⟨b, hb⟩
      exact Or.inr ⟨b, by apply Subtype.ext; exact hb.symm⟩
  · intro a b
    constructor
    · intro hab
      exfalso
      have hmemA : iA a ∈ Set.range iA := ⟨a, rfl⟩
      have hmemB : iA a ∈ Set.range iB := by
        refine ⟨b, ?_⟩
        exact congrArg Subtype.val hab |>.symm
      exact (Set.disjoint_left.mp hDisj) hmemA hmemB
    · rintro ⟨d, _ha, _hb⟩
      exact PEmpty.elim d
  · intro sym z
    constructor
    · intro hz
      have hzR : R.rel sym (Subtype.val ∘ z) := hz
      have hzUnion :
          ∀ k, (Subtype.val ∘ z) k ∈
            Set.range iA ∪ Set.range iB :=
        fun k => (z k).2
      rcases hSplit sym (Subtype.val ∘ z) hzR hzUnion with hA | hB
      · let x : Fin (L.arity sym) → W :=
          fun k => Classical.choose (hA k)
        have hx (k : Fin (L.arity sym)) :
            iA (x k) = (z k).1 :=
          Classical.choose_spec (hA k)
        have hxrel : A.rel sym x := by
          apply (iA.map_rel_iff sym x).mp
          have htup :
              iA.toFun ∘ x = Subtype.val ∘ z := by
            funext k
            exact hx k
          rw [htup]
          exact hzR
        refine Or.inl ⟨x, hxrel, ?_⟩
        funext k
        apply Subtype.ext
        exact (hx k).symm
      · let x : Fin (L.arity sym) → V :=
          fun k => Classical.choose (hB k)
        have hx (k : Fin (L.arity sym)) :
            iB (x k) = (z k).1 :=
          Classical.choose_spec (hB k)
        have hxrel : B.rel sym x := by
          apply (iB.map_rel_iff sym x).mp
          have htup :
              iB.toFun ∘ x = Subtype.val ∘ z := by
            funext k
            exact hx k
          rw [htup]
          exact hzR
        refine Or.inr ⟨x, hxrel, ?_⟩
        funext k
        apply Subtype.ext
        exact (hx k).symm
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact
          ((leftToInducedImageUnion iA iB).map_rel_iff sym x).mpr hx
      · exact
          ((rightToInducedImageUnion iA iB).map_rel_iff sym x).mpr hx

end StructuralRamsey.Girth
