import Girth.FiniteTraceRelationalExtraction
import Girth.ForestCompletionPhysicalSet
import Girth.ForestMixedSetBound
import Girth.ForestPhysicalABCompletion
import Girth.ForestReindex
import Girth.SharedSupport

/-!
# Small induced structures in the actual final picture

Use the designated B-carriers as the trace-cover indices. A completion of
a request of B-carriers uses only B-carriers, because every added member
is designated B. The B-carrier is recoverable from its full support piece,
so the support forest can be reindexed on the actual completed carriers.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- The bounded mixed-forest conclusion of a picture step gives physical
forest completion whenever all eligible supports belong to its tested family.
The requested physical family itself suffices. -/
theorem PhysicalCopySetForestExtension.of_boundedMixedForests
    {W Phys : Type v} {support : Phys → HypergraphPiece W}
    {eligible designated : Phys → Prop}
    {tested : HypergraphPiece W → Prop} {m : ℕ}
    (hForest : FiniteMixedForestThrough tested m)
    (hTest : ∀ p, eligible p → tested (support p)) :
    PhysicalCopySetForestExtension support eligible designated m := by
  classical
  intro N hEligible hCard
  refine ⟨N, Finset.Subset.rfl, fun _ hp => Or.inl hp, ?_⟩
  apply hForest (N.image support)
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact hTest p (hEligible p hp)
  · exact Finset.card_image_le.trans hCard

/-- Restrict a physical completion property to a finite family whose
support keys are distinct and which contains all permitted additions. -/
theorem finiteForestCompletion_of_physicalKeys
    {W Phys I : Type v} [Fintype I]
    {support : Phys → HypergraphPiece W}
    {eligible designated : Phys → Prop} {m : ℕ}
    (hComplete : PhysicalCopySetForestExtension support eligible designated m)
    (key : I → Phys)
    (hEligible : ∀ i, eligible (key i))
    (hDesignated : ∀ p, designated p → ∃ i, key i = p)
    (hInj : Function.Injective (support ∘ key))
    (N : Finset I) (hN : N.card ≤ m) :
    ∃ S : Finset I, N ⊆ S ∧
      ForestOfCopies (fun i : {i // i ∈ S} => support (key i.val)) := by
  classical
  let request := N.image key
  have hRequestEligible : ∀ p, p ∈ request → eligible p := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hEligible i
  have hRequestCard : request.card ≤ m := Finset.card_image_le.trans hN
  obtain ⟨completed, hContains, hOnly, hForest⟩ :=
    hComplete request hRequestEligible hRequestCard
  let S := Finset.univ.filter (fun i => key i ∈ completed)
  have hSub : N ⊆ S := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hContains (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
  let toSupport (i : {i // i ∈ S}) : {P // P ∈ completed.image support} :=
    ⟨support (key i.val),
      Finset.mem_image.mpr ⟨key i.val, (Finset.mem_filter.mp i.property).2, rfl⟩⟩
  have hToSupportInj : Function.Injective toSupport := by
    intro i j h
    apply Subtype.ext
    exact hInj (congrArg Subtype.val h)
  have hToSupportSurj : Function.Surjective toSupport := by
    intro P
    obtain ⟨p, hp, hPiece⟩ := Finset.mem_image.mp P.property
    have hKey : ∃ i, key i = p := by
      rcases hOnly p hp with hRequested | hAdded
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hRequested
        exact ⟨i, hi⟩
      · exact hDesignated p hAdded
    obtain ⟨i, hi⟩ := hKey
    have hMem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm ▸ hp⟩
    refine ⟨⟨i, hMem⟩, Subtype.ext ?_⟩
    change support (key i) = P.val
    exact (congrArg support hi).trans hPiece
  let e := Equiv.ofBijective toSupport ⟨hToSupportInj, hToSupportSurj⟩
  exact ⟨S, hSub, hForest.reindex e⟩

variable {L : RelLanguage.{u}} {UA VB P X : Type v}

private theorem irreducible_induce_of_subsingleton
    (R : RelStructure L X) (T : Set X) (hT : T.Subsingleton) :
    (R.induce T).Irreducible := by
  intro x y hxy
  exact (hxy (Subtype.ext (hT x.property y.property))).elim

private theorem irreducible_induce_tuple_range
    (R : RelStructure L X) (r : L.Symbol) (t : Fin (L.arity r) → X)
    (ht : R.rel r t) :
    (R.induce (Set.range t)).Irreducible := by
  intro x y _
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨j, hj⟩ := y.property
  let lifted (k : Fin (L.arity r)) : Set.range t := ⟨t k, ⟨k, rfl⟩⟩
  exact ⟨r, lifted, i, j, ht, Subtype.ext hi, Subtype.ext hj⟩

/-- The small-induced-structure consequence for the actual picture.
Its assumptions are the physical forest-extension, designated irreducible
coverage and shared support maintained by the outer construction. -/
theorem smallInducedStructure_embeds_supportedTree_of_picture
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    [Finite X]
    (family : Set (Embedding B D))
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hShared : DesignatedSharedSupport A C family)
    (q : ℕ) (hq : 1 ≤ q)
    (hComplete : PhysicalCopySetForestExtension
      (pictureABPhysicalSupport A C.toRelStructure)
      (pictureABPhysicalEligible A B D C family)
      (pictureABPhysicalDesignated B D C family) q)
    (Z : Set X) (hBudget : Z.ncard ≤ q)
    (alphaB : Embedding A B) (a₀ a₁ : UA) (hne : a₀ ≠ a₁) :
    ∃ (Y : Type v) (T : RelStructure L Y)
        (_ : Embedding (C.toRelStructure.induce Z) T),
      ASupportedTreeAmalgam A B Y T := by
  classical
  let Keys := {V : Set X // ∃ c : DesignatedCopy B D C family, copyCarrier c.embedding = V}
  let rep (i : Keys) : DesignatedCopy B D C family := Classical.choose i.property
  let member (i : Keys) : ABMember A B C.toRelStructure := .b (rep i).embedding
  let key (i : Keys) : Set X ⊕ Set X := Sum.inr i.val
  let mkKey (c : DesignatedCopy B D C family) : Keys := ⟨copyCarrier c.embedding, ⟨c, rfl⟩⟩
  have hRepCarrier (i : Keys) : copyCarrier (rep i).embedding = i.val :=
    Classical.choose_spec i.property
  have hMemberCarrier (i : Keys) : (member i).carrier = i.val := hRepCarrier i
  have hPiece (i : Keys) :
      (member i).supportPiece A = pictureABPhysicalSupport A C.toRelStructure (key i) := by
    change physicalBCarrierSupport A C.toRelStructure (copyCarrier (rep i).embedding) =
      physicalBCarrierSupport A C.toRelStructure i.val
    rw [hRepCarrier]
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Keys := Fintype.ofFinite Keys
  obtain ⟨c₀, _⟩ := hCover ∅ (irreducible_induce_of_subsingleton _ _ Set.subsingleton_empty)
  letI : Nonempty Keys := ⟨mkKey c₀⟩
  have hVertices : ∀ x ∈ Z, ∃ i, x ∈ (member i).carrier := by
    intro x _
    have hIrr := irreducible_induce_of_subsingleton C.toRelStructure
      ({x} : Set X) Set.subsingleton_singleton
    obtain ⟨c, hc⟩ := hCover {x} hIrr
    obtain ⟨b, hb⟩ := hc ⟨x, Set.mem_singleton x⟩
    exact ⟨mkKey c, (hMemberCarrier (mkKey c)).symm ▸ ⟨b, hb.symm⟩⟩
  have hRelations : ∀ (r : L.Symbol), 0 < L.arity r →
      ∀ t : Fin (L.arity r) → Z, C.toRelStructure.rel r (Subtype.val ∘ t) →
        ∃ i, ∀ j, (t j).val ∈ (member i).carrier := by
    intro r _ t ht
    obtain ⟨c, hc⟩ := hCover (Set.range (Subtype.val ∘ t))
      (irreducible_induce_tuple_range C.toRelStructure r _ ht)
    refine ⟨mkKey c, fun j => ?_⟩
    obtain ⟨b, hb⟩ := hc ⟨(t j).val, ⟨j, rfl⟩⟩
    exact (hMemberCarrier (mkKey c)).symm ▸ ⟨b, hb.symm⟩
  have hMemberShared : PairwiseMixedSharedVerticesSupported A member := by
    intro i j hij x hxi hxj
    have hNe : rep i ≠ rep j := by
      intro he
      apply hij
      apply Subtype.ext
      calc
        i.val = copyCarrier (rep i).embedding := (hRepCarrier i).symm
        _ = copyCarrier (rep j).embedding := congrArg (fun c => copyCarrier c.embedding) he
        _ = j.val := hRepCarrier j
    obtain ⟨hi, hj⟩ := hShared.2 (rep i) (rep j) hNe x hxi hxj
    have supportFromRep (k : Keys) (hk : VertexSupportedInDesignated A (rep k) x) :
        (member k).VertexSupported A x := by
      obtain ⟨a, ha⟩ := hk
      refine ⟨(rep k).embedding.comp a, ha, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact ⟨a b, rfl⟩
    exact ⟨supportFromRep i hi, supportFromRep j hj⟩
  have hOrdinaryCompletion : ∀ N : Finset Keys, N.Nonempty → N.card ≤ q →
      ∃ S : Finset Keys, N ⊆ S ∧
        ForestOfCopies (fun i : {j // j ∈ S} => (member i.val).supportPiece A) := by
    intro N _ hN
    have hEligible (i : Keys) : pictureABPhysicalEligible A B D C family (key i) :=
      i.property
    have hDesignated (p : Set X ⊕ Set X)
        (hp : pictureABPhysicalDesignated B D C family p) : ∃ i : Keys, key i = p := by
      cases p with
      | inl _ => exact False.elim hp
      | inr V => exact ⟨⟨V, hp⟩, rfl⟩
    have hInj : Function.Injective (pictureABPhysicalSupport A C.toRelStructure ∘ key) := by
      intro i j h
      apply Subtype.ext
      exact congrArg HypergraphPiece.carrier h
    obtain ⟨S, hSub, hForest⟩ :=
      finiteForestCompletion_of_physicalKeys hComplete key hEligible hDesignated hInj N hN
    exact ⟨S, hSub, by simpa only [hPiece] using hForest⟩
  exact smallInducedStructure_embeds_supportedTree_of_forestCompletion
    C.toRelStructure member Z q hq hBudget hVertices hRelations hMemberShared
    hOrdinaryCompletion alphaB a₀ a₁ hne

/-- Consume the support-indexed forest invariant used in the actual
picture-increment theorem. No separate physical completion is required. -/
theorem smallInducedStructure_embeds_supportedTree_of_assembledPicture
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    [Finite X]
    (family : Set (Embedding B D))
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hShared : DesignatedSharedSupport A C family)
    (q : ℕ) (hq : 1 ≤ q)
    (hComplete : ForestCompletionProperty
      (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family) q)
    (Z : Set X) (hBudget : Z.ncard ≤ q)
    (alphaB : Embedding A B) (a₀ a₁ : UA) (hne : a₀ ≠ a₁) :
    ∃ (Y : Type v) (T : RelStructure L Y)
        (_ : Embedding (C.toRelStructure.induce Z) T),
      ASupportedTreeAmalgam A B Y T := by
  apply smallInducedStructure_embeds_supportedTree_of_picture
    A B D C family hCover hShared q hq _ Z hBudget alphaB a₀ a₁ hne
  apply hComplete.toPhysicalCopySet
  · intro p hp
    cases p with
    | inl V =>
      obtain ⟨a, hCarrier⟩ := hp
      exact Or.inl ⟨a, congrArg HypergraphPiece.oneEdge hCarrier.symm⟩
    | inr V =>
      exact Or.inr (pictureABPhysicalDesignated_support A B D C family (Sum.inr V) hp)
  · intro T hT
    obtain ⟨c, hEq⟩ := hT
    exact ⟨Sum.inr (copyCarrier c.embedding), ⟨c, rfl⟩, hEq.symm⟩

/-- The outer construction may choose the target itself. In that case
each induced structure embeds into the one-member tree amalgam. -/
theorem smallInducedStructure_embeds_supportedTree_in_target
    (A : RelStructure L UA) (B : RelStructure L VB) (Z : Set VB) :
    ∃ (Y : Type v) (T : RelStructure L Y) (_ : Embedding (B.induce Z) T),
      ASupportedTreeAmalgam A B Y T :=
  ⟨VB, B, RelStructure.inclusion B Z, ASupportedTreeAmalgam.copy (Iso.refl B)⟩

end StructuralRamsey.Girth
