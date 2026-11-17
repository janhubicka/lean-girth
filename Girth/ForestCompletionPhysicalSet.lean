import Girth.ForestMixedSetBound
import Girth.ForestPhysicalCopySetCompletion
import Girth.ForestReindex
import Girth.ForestTreeRewire

/-!
# From an assembled forest to a set of physical copies

A labelled completion can repeat an identical support piece. Erasing a
duplicate keeps its entire carrier in the surviving occurrence, so the
existing join-tree rewiring theorem applies. This makes the physical-set
and support-indexed forms of the outer forest invariant compatible.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- A forest of pieces yields a forest on the distinct values of its
pieces. Removing duplicates uses a surviving copy of the entire
deleted piece carrier. -/
theorem ForestOfCopies.distinctSupportImage
    {I : Type v} [Fintype I] {F : I → HypergraphPiece W}
    (hForest : ForestOfCopies F) :
    ForestOfCopies (fun P : {P // P ∈ finitePieceImage F} => P.val) := by
  classical
  by_cases hInj : Function.Injective F
  · let encode (i : I) : {P // P ∈ finitePieceImage F} :=
      ⟨F i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hEncodeInj : Function.Injective encode := by
      intro a b h
      exact hInj (congrArg Subtype.val h)
    have hEncodeSurj : Function.Surjective encode := by
      intro P
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp P.property
      exact ⟨i, Subtype.ext hi⟩
    let e := Equiv.ofBijective encode ⟨hEncodeInj, hEncodeSurj⟩
    convert hForest.reindex e.symm using 1
    funext P
    exact congrArg Subtype.val (e.apply_symm_apply P).symm
  · simp only [Function.Injective, not_forall] at hInj
    obtain ⟨i, j, hEq, hNe⟩ := hInj
    letI : Nonempty I := ⟨i⟩
    obtain ⟨J⟩ := hForest.joinTree_of_nonempty
    let Rest := {k : I // k ∈ (({i} : Set I)ᶜ)}
    have hJRest : Nonempty (JoinTree (erasePiece F i)) :=
      J.nonempty_eraseMember_of_full (center := i) (hub := j) (fun he => hNe he.symm)
        (by simpa only [hEq] using (Set.Subset.rfl : (F j).carrier ⊆ (F j).carrier))
    have hRest : ForestOfCopies (erasePiece F i) := by
      refine ⟨?_, Or.inr hJRest⟩
      intro a b hab
      exact hForest.pairwiseAllowed (fun he => hab (Subtype.ext he))
    have hCard : Fintype.card Rest < Fintype.card I := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun k : Rest => k.val) Subtype.val_injective
      intro hSurj
      obtain ⟨k, hk⟩ := hSurj i
      exact k.property (Set.mem_singleton_iff.mpr hk)
    have hSame : finitePieceImage (erasePiece F i) = finitePieceImage F := by
      ext P
      constructor
      · intro hP
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hP
        exact Finset.mem_image.mpr ⟨k.val, Finset.mem_univ _, hk⟩
      · intro hP
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hP
        by_cases hki : k = i
        · subst k
          exact Finset.mem_image.mpr
            ⟨⟨j, fun h => hNe (Set.mem_singleton_iff.mp h).symm⟩, Finset.mem_univ _,
              hEq.symm.trans hk⟩
        · exact Finset.mem_image.mpr
            ⟨⟨k, fun h => hki (Set.mem_singleton_iff.mp h)⟩, Finset.mem_univ _, hk⟩
    rw [← hSame]
    exact hRest.distinctSupportImage
termination_by Fintype.card I
decreasing_by exact hCard

/-- A labelled support completion gives a faithful physical-set
completion when the tested supports and allowed additions come from the
physical eligibility predicates. -/
theorem ForestCompletionProperty.toPhysicalCopySet
    {Phys : Type v} {support : Phys → HypergraphPiece W}
    {eligible physicalDesignated : Phys → Prop}
    {tested designated : HypergraphPiece W → Prop} {m : ℕ}
    (hCompletion : ForestCompletionProperty tested designated m)
    (hTest : ∀ p, eligible p → tested (support p))
    (hDesignated : ∀ P, designated P → ∃ p, physicalDesignated p ∧ support p = P) :
    PhysicalCopySetForestExtension support eligible physicalDesignated m := by
  classical
  intro N hEligible hCard
  let Request := {p : Phys // p ∈ N}
  obtain ⟨K, instK, completed, hWitness⟩ :=
    hCompletion Request (fun p => support p.val)
      (fun p => hTest p.val (hEligible p.val p.property)) (by simpa [Request] using hCard)
  letI : Fintype K := instK
  have hPhysical (k : K) :
      ∃ p, (p ∈ N ∨ physicalDesignated p) ∧ support p = completed k := by
    rcases hWitness.2.2 k with ⟨p, hp⟩ | hDel
    · exact ⟨p.val, Or.inl p.property, hp.symm⟩
    · obtain ⟨p, hp, hEq⟩ := hDesignated _ hDel
      exact ⟨p, Or.inr hp, hEq⟩
  choose physical hClass hSupport using hPhysical
  let S := N ∪ Finset.univ.image physical
  have hImage : S.image support = finitePieceImage completed := by
    ext P
    constructor
    · intro hP
      obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp hP
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨k, hk⟩ := hWitness.2.1 ⟨p, hp⟩
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.trans hEq⟩
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, (hSupport k).symm.trans hEq⟩
    · intro hP
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hP
      refine Finset.mem_image.mpr ⟨physical k, ?_, (hSupport k).trans hk⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  refine ⟨S, Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Or.inl hp
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
      exact hClass k
  · rw [hImage]
    exact hWitness.1.distinctSupportImage

end StructuralRamsey.Girth
