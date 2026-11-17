import Girth.FunctionalEHNClass

set_option autoImplicit false
set_option Elab.async false

/-!
The cutoff-two local core must cover its irreducibles by actual A-copies.
For nonsingleton irreducibles this restriction defines a free amalgamation
subclass of the canonical elementary-closure class. An embedding of closed
structures pulls an A-copy back as soon as two of its vertices are in its
range. Coverage of singleton and empty irreducibles is separate because
substructures may contain isolated points or be empty.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA V W : Type v}

/-- The hereditary form of irreducible A-coverage. -/
def NonsingletonIrreduciblesExtendTo (A : RelStructure L UA)
    (R : RelStructure L V) : Prop :=
  ∀ (S : Set V), (R.induce S).Irreducible → ¬ S.Subsingleton →
    ∃ a : Embedding A R, S ⊆ copyCarrier a

/-- A nonempty, support-covered core also covers its empty and singleton
irreducibles. These two cases need no additional class constraint. -/
theorem NonsingletonIrreduciblesExtendTo.with_support
    {A : RelStructure L UA} {R : RelStructure L V}
    (hCover : NonsingletonIrreduciblesExtendTo A R)
    (hNonempty : Nonempty (Embedding A R))
    (hVertex : ∀ x : V, ∃ a : Embedding A R, x ∈ copyCarrier a) :
    IrreduciblesExtendTo A R := by
  classical
  intro T hT
  by_cases hSmall : T.Subsingleton
  · by_cases hTNonempty : T.Nonempty
    · obtain ⟨x, hx⟩ := hTNonempty
      obtain ⟨a, u, hu⟩ := hVertex x
      exact ⟨a, fun z => ⟨u, (hSmall z.2 hx).trans hu.symm⟩⟩
    · obtain ⟨a⟩ := hNonempty
      exact ⟨a, fun z => (hTNonempty ⟨z.1, z.2⟩).elim⟩
  · obtain ⟨a, ha⟩ := hCover T hT hSmall
    refine ⟨a, ?_⟩
    intro z
    obtain ⟨u, hu⟩ := ha z.2
    exact ⟨u, hu.symm⟩

private theorem cover_embedded_irreducible_range
    {A : RelStructure L UA} {R : RelStructure L V} {D : RelStructure L W}
    (hCover : NonsingletonIrreduciblesExtendTo A D)
    {T : Set V} (hT : (R.induce T).Irreducible) (hLarge : ¬ T.Subsingleton)
    (f : Embedding (R.induce T) D) :
    ∃ a : Embedding A D, Set.range f ⊆ copyCarrier a := by
  refine hCover (Set.range f) (hT.range_embedding f) ?_
  intro hSmall
  apply hLarge
  intro x hx y hy
  exact congrArg Subtype.val <| f.injective <|
    hSmall ⟨⟨x, hx⟩, rfl⟩ ⟨⟨y, hy⟩, rfl⟩

/-- Nonsingleton coverage pulls back along an induced A-strong embedding. -/
theorem NonsingletonIrreduciblesExtendTo.of_strong_embedding
    {A : RelStructure L UA} {R : RelStructure L V} {D : RelStructure L W}
    (hCover : NonsingletonIrreduciblesExtendTo A D)
    (f : Embedding R D) (hStrong : AStrong A D (copyCarrier f)) :
    NonsingletonIrreduciblesExtendTo A R := by
  classical
  intro T hT hLarge
  let g := f.comp (RelStructure.inclusion R T)
  obtain ⟨a, hCovered⟩ := cover_embedded_irreducible_range hCover hT hLarge g
  have hInter : ¬ (copyCarrier a ∩ copyCarrier f).Subsingleton := by
    intro hSmall
    apply hLarge
    intro x hx y hy
    have hMem (z : T) : f z.1 ∈ copyCarrier a ∩ copyCarrier f :=
      ⟨hCovered ⟨z, rfl⟩, ⟨z.1, rfl⟩⟩
    exact f.injective (hSmall (hMem ⟨x, hx⟩) (hMem ⟨y, hy⟩))
  have hSub := hStrong a hInter
  have hFactor (u : UA) : ∃ x : V, a u = f x := by
    obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
    exact ⟨x, hx.symm⟩
  let aR := a.factorThroughRange f hFactor
  refine ⟨aR, ?_⟩
  intro x hx
  have hxCover : g ⟨x, hx⟩ ∈ copyCarrier a := hCovered ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨u, hu⟩ := hxCover
  have hBase : a u = f (aR u) := Classical.choose_spec (hFactor u)
  exact ⟨u, f.injective (hBase.symm.trans hu)⟩

/-- In a free amalgam every irreducible lies wholly within one side,
so its A-coverage transports from that side. -/
theorem nonsingletonIrreduciblesExtendTo_of_freeAmalgam
    {H V₁ V₂ V₀ : Type v}
    {A : RelStructure L UA} {C : RelStructure L V₀}
    {Base : RelStructure L H}
    {B₁ : RelStructure L V₁} {B₂ : RelStructure L V₂}
    {s₁ : Embedding Base B₁} {s₂ : Embedding Base B₂}
    {i₁ : Embedding B₁ C} {i₂ : Embedding B₂ C}
    (hFree : IsFreeAmalgam s₁ s₂ i₁ i₂)
    (h₁ : NonsingletonIrreduciblesExtendTo A B₁)
    (h₂ : NonsingletonIrreduciblesExtendTo A B₂) :
    NonsingletonIrreduciblesExtendTo A C := by
  classical
  intro T hT hLarge
  have pushCoverage {Z : Type v} {D : RelStructure L Z}
      (i : Embedding D C) (hCover : NonsingletonIrreduciblesExtendTo A D)
      (hSub : ∀ z : T, ∃ w : Z, z.1 = i w) :
      ∃ a : Embedding A C, T ⊆ copyCarrier a := by
    let e := (RelStructure.inclusion C T).factorThroughRange i hSub
    obtain ⟨a, ha⟩ := cover_embedded_irreducible_range hCover hT hLarge e
    refine ⟨i.comp a, ?_⟩
    intro z hz
    have hzCover : e ⟨z, hz⟩ ∈ copyCarrier a := ha ⟨⟨z, hz⟩, rfl⟩
    obtain ⟨u, hu⟩ := hzCover
    have hzSpec : z = i (e ⟨z, hz⟩) :=
      Classical.choose_spec (hSub ⟨z, hz⟩)
    exact ⟨u, (congrArg i hu).trans hzSpec.symm⟩
  rcases hFree.irreducible_side T hT with hLeft | hRight
  · exact pushCoverage i₁ h₁ hLeft
  · exact pushCoverage i₂ h₂ hRight

/-- The EHN class with nonsingleton irreducible A-coverage. -/
def CoveredElementaryCAClass (A : RelStructure L UA) :
    StructuralRamsey.Structure.StructureClass (L := closureLanguage L) :=
  fun C => ElementaryCAClass A C ∧
    NonsingletonIrreduciblesExtendTo A (closureRelReduct C)

theorem CoveredElementaryCAClass_freeAmalgamationClass
    (A : RelStructure L UA) (hA : A.Irreducible) :
    StructuralRamsey.Structure.FreeAmalgamationClass (CoveredElementaryCAClass A) where
  hereditary := by
    intro _ _ _ _ hD e
    exact ⟨(ElementaryCAClass_freeAmalgamationClass A hA).hereditary hD.1 e,
      hD.2.of_strong_embedding (closureEmbeddingRel e)
        (closureEmbedding_range_aStrong hD.1.2 e)⟩
  free := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight hFree
    exact ⟨(ElementaryCAClass_freeAmalgamationClass A hA).free
        hLeft.1 hRight.1 hFree,
      nonsingletonIrreduciblesExtendTo_of_freeAmalgam
        (closureFreeAmalgamRel hFree) hLeft.2 hRight.2⟩

end StructuralRamsey.Girth
