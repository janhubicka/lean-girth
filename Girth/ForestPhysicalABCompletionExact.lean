import Girth.ForestFiniteImage
import Girth.ForestPhysicalABCompletion

/-! # Exact passage between physical requests and support completions -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {W Phys : Type v}

/-- An indexed completion gives a completion of the original copy set.
Choose an actual designated copy for each added support piece and retain
every requested copy, including copies with equal supports. -/
theorem ForestCompletionProperty.toPhysicalCopySet
    {support : Phys → HypergraphPiece W} {eligible designated : Phys → Prop}
    {tested allowed : HypergraphPiece W → Prop} {m : ℕ}
    (hComplete : ForestCompletionProperty tested allowed m)
    (hTested : ∀ p, eligible p → tested (support p))
    (hDesignated : ∀ T, allowed T → ∃ p, designated p ∧ support p = T) :
    PhysicalCopySetForestExtension support eligible designated m := by
  classical
  intro s hEligible hBudget
  let Requests := {p : Phys // p ∈ s}
  letI : Fintype Requests := Finset.fintypeCoeSort s
  obtain ⟨K, finite, completed, hForest, hContains, hClassify⟩ :=
    hComplete Requests (fun p => support p.1)
      (fun p => hTested p.1 (hEligible p.1 p.2)) (by
        change Fintype.card (↥s) ≤ m
        simpa only [Fintype.card_coe] using hBudget)
  letI : Fintype K := finite
  have hLift (k : K) : ∃ p, (p ∈ s ∨ designated p) ∧ support p = completed k := by
    rcases hClassify k with ⟨p, heq⟩ | hAllowed
    · exact ⟨p.1, Or.inl p.2, heq.symm⟩
    · obtain ⟨p, hp, heq⟩ := hDesignated (completed k) hAllowed
      exact ⟨p, Or.inr hp, heq⟩
  choose represented hRepresented hSupport using hLift
  let t : Finset Phys := s ∪ Finset.univ.image represented
  refine ⟨t, Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hs | hr
    · exact Or.inl hs
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
      exact hRepresented k
  · have hImage : t.image support = Finset.univ.image completed := by
      ext T
      constructor
      · rintro hT
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hT
        rcases Finset.mem_union.mp hp with hs | hr
        · obtain ⟨k, hk⟩ := hContains ⟨p, hs⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, (hSupport k).symm⟩
      · intro hT
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hT
        exact Finset.mem_image.mpr ⟨represented k,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩),
          hSupport k⟩
    rw [hImage]
    exact hForest.finiteImage completed

variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- The finite sets of actual A/B copies and the indexed full-support
invariant give equivalent forest-completion assertions. -/
theorem pictureABPhysicalForestExtension_iff
    (A : RelStructure L UA) (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X) (family : Set (Embedding B D))
    (m : ℕ) :
    PhysicalCopySetForestExtension (pictureABPhysicalSupport A C.toRelStructure)
      (pictureABPhysicalEligible A B D C family) (pictureABPhysicalDesignated B D C family) m ↔
    ForestCompletionProperty (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family) m := by
  constructor
  · intro hPhysical
    apply (hPhysical.toLabelFinset (pictureABPhysicalKey A B D C family)
      (pictureABLabelSupport A B D C family) (fun _ => True)
      (pictureABLabelSupport_eq_physicalSupport A B D C family)
      (fun label _ => pictureABPhysicalKey_eligible A B D C family label)
      (pictureABPhysicalDesignated_support A B D C family)).toSupportIndexed
    intro T hT
    obtain ⟨label, hLabel⟩ := (testedPictureABSupport_iff_label A B D C family T).mp hT
    exact ⟨label, trivial, hLabel⟩
  · intro hComplete
    apply hComplete.toPhysicalCopySet
    · intro key hEligible
      cases key with
      | inl V =>
          obtain ⟨a, rfl⟩ := hEligible
          exact Or.inl ⟨a, rfl⟩
      | inr V =>
          obtain ⟨q, rfl⟩ := hEligible
          exact Or.inr ⟨q, rfl⟩
    · rintro T ⟨q, rfl⟩
      exact ⟨.inr (copyCarrier q.embedding), ⟨q, rfl⟩, rfl⟩

end StructuralRamsey.Girth
