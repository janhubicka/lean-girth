import Girth.ALinearRamsey
import Girth.TrainRecursiveAllowedPredicates

set_option autoImplicit false

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The EHN base and its strong selected family for the unrestricted
conversion. The auxiliary order need only extend the target order. -/
theorem exists_orderRamseyBase_of_extendsOrder
    (A₀ : RelStructure L UA) [Finite UA] [LinearOrder UA]
    (B : RelStructure L.withOrder VB) [Finite VB] [LinearOrder VB]
    (hExtends : B.ExtendsOrder) (hLinear : ALinear A₀.ordered B)
    (κ : Type w) [Fintype κ] [Nonempty κ]
    {J : Type*} (symbols : J → Set L.Symbol) :
    ∃ (W : Type v) (_ : Finite W) (D : RelStructure L.withOrder W)
        (family : Set (Embedding B D)),
      ALinear A₀.ordered D ∧
      (∀ b ∈ family, AStrong A₀.ordered D (copyCarrier b)) ∧
      (∀ b ∈ family, ∀ j : J,
        b ⁻¹' allowedByPredicates D symbols j = allowedByPredicates B symbols j) ∧
      (∀ χ : Embedding A₀.ordered D → κ,
        ∃ b ∈ family, ∀ a a' : Embedding A₀.ordered B,
          χ (b.comp a) = χ (b.comp a')) := by
  have hMono (a : Embedding A₀.ordered B) : StrictMono a :=
    (a.completeOrder hExtends).strictMono
  obtain ⟨W, hW, _order, C, hC, hArrow⟩ :=
    closedTargetRamseyFamily_of_monotone_embeddings A₀.ordered B
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible hLinear hMono κ
  let D := closureRelReduct C
  let family : Set (Embedding B D) :=
    Set.range (fun b : Structure.Embedding (targetClosureExpansion A₀.ordered B) C =>
      targetEmbeddingRel b)
  refine ⟨W, hW, D, family, hC.1, ?_, ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact targetEmbedding_range_aStrong hC.2 b
  · intro b _ j
    exact allowedByPredicates_pullback b symbols j
  · intro χ
    obtain ⟨b, hb⟩ := hArrow χ
    exact ⟨targetEmbeddingRel b, ⟨b, rfl⟩, hb⟩

/-- Three source embeddings with cyclically consecutive endpoints obstruct
the Ramsey arrow under a two-colouring, for every finite ambient structure. -/
theorem no_arrow_of_cyclic_edge_embeddings
    {A : RelStructure L UA} {B : RelStructure L VB} {C : RelStructure L P}
    [Finite P] (x y : UA) (hxy : x ≠ y) (a b c : Embedding A B)
    (hab : a y = b x) (hbc : b y = c x) (hca : c y = a x) :
    ¬ StructuralRamsey.Arrow A B C Bool := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let number := Fintype.equivFin P
  let colour (f : Embedding A C) : Bool :=
    decide (number (f x) < number (f y))
  intro h
  obtain ⟨f, hf⟩ := h colour
  let i := number (f (a x))
  let j := number (f (b x))
  let k := number (f (c x))
  have hij : i ≠ j := by
    intro heq
    apply hxy
    apply a.injective
    exact (f.injective (number.injective heq)).trans hab.symm
  have hjk : j ≠ k := by
    intro heq
    apply hxy
    apply b.injective
    exact (f.injective (number.injective heq)).trans hbc.symm
  have hki : k ≠ i := by
    intro heq
    apply hxy
    apply c.injective
    exact (f.injective (number.injective heq)).trans hca.symm
  have h₁ : decide (i < j) = decide (j < k) := by
    simpa only [colour, Embedding.comp_apply, hab, hbc, i, j, k] using hf a b
  have h₂ : decide (j < k) = decide (k < i) := by
    simpa only [colour, Embedding.comp_apply, hbc, hca, i, j, k] using hf b c
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [decide_eq_true hlt] at h₁
    have hjk' : j < k := of_decide_eq_true h₁.symm
    have hki' : k < i := of_decide_eq_true (h₁.trans h₂).symm
    exact lt_irrefl i (hlt.trans (hjk'.trans hki'))
  · have hi : decide (i < j) = false := by simp [not_lt_of_gt hgt]
    rw [hi] at h₁
    have hkj : k < j := lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false h₁.symm)) hjk.symm
    have hik : i < k :=
      lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false (h₁.trans h₂).symm)) hki.symm
    exact lt_irrefl i (hik.trans (hkj.trans hgt))

end StructuralRamsey.Girth.TrainRecursiveWitness
