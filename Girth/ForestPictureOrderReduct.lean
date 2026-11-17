import Girth.FiniteTraceOrderReduct

/-! # The mixed completion union after forgetting the order -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- The amalgamation union of a physical family contains an ambient tuple
exactly when a member carrier contains every entry. -/
def physicalFamilyUnion {I : Type v} (R : RelStructure L X)
    (support : I → HypergraphPiece X) (S : Finset I) :
    RelStructure L {x : X // ∃ p ∈ S, x ∈ (support p).carrier} where
  rel r t := R.rel r (Subtype.val ∘ t) ∧
    ∃ p ∈ S, ∀ i, (t i).val ∈ (support p).carrier

/-- Every nonempty finite physical request admits a designated-only
completion whose whole amalgamation union, after forgetting the order,
embeds into an unordered supported tree amalgam of the target. -/
theorem mixedFamilyUnion_orderReduct_of_nonempty_request
    {A : RelStructure L.withOrder UA} {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P} {C : StructuralRamsey.Partite.System L.withOrder P X}
    {family : Set (Embedding B D)}
    (hShared : DesignatedSharedSupport A C family)
    (q : ℕ)
    (hComplete : ForestCompletionProperty
      (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family) q)
    (S : Finset (Set X ⊕ Set X)) (hNonempty : S.Nonempty)
    (hEligible : ∀ p ∈ S, pictureABPhysicalEligible A B D C family p)
    (hBudget : S.card ≤ q)
    (alpha : Embedding A B) (a₀ a₁ : UA) (hne : a₀ ≠ a₁) :
    ∃ T : Finset (Set X ⊕ Set X), S ⊆ T ∧
      (∀ p ∈ T, p ∈ S ∨ pictureABPhysicalDesignated B D C family p) ∧
      ∃ (Y : Type v) (R : RelStructure L Y)
        (_ : Embedding (physicalFamilyUnion C.toRelStructure.orderReduct
          (pictureABPhysicalSupport A C.toRelStructure) T) R),
        ASupportedTreeAmalgam A.orderReduct B.orderReduct Y R := by
  classical
  let support := pictureABPhysicalSupport A C.toRelStructure
  have hPhysical : PhysicalCopySetForestExtension support
      (pictureABPhysicalEligible A B D C family)
      (pictureABPhysicalDesignated B D C family) q := by
    apply hComplete.toPhysicalCopySet
    · intro p hp
      cases p with
      | inl V =>
        obtain ⟨a, ha⟩ := hp
        exact Or.inl ⟨a, congrArg HypergraphPiece.oneEdge ha.symm⟩
      | inr V =>
        exact Or.inr (pictureABPhysicalDesignated_support A B D C family (.inr V) hp)
    · intro M hM
      obtain ⟨c, hc⟩ := hM
      exact ⟨.inr (copyCarrier c.embedding), ⟨c, rfl⟩, hc.symm⟩
  obtain ⟨T, hSub, hOnly, hForest⟩ := hPhysical S hEligible hBudget
  let Keys := {p : HypergraphPiece X // p ∈ T.image support}
  let Label := Embedding A C.toRelStructure ⊕ DesignatedCopy B D C family
  let member : Label → ABMember A B C.toRelStructure
    | .inl a => .a a
    | .inr c => .b c.embedding
  have hTEligible (p) (hp : p ∈ T) : pictureABPhysicalEligible A B D C family p := by
    rcases hOnly p hp with h | h
    · exact hEligible p h
    · cases p with
      | inl V => exact False.elim h
      | inr V => exact h
  have hRepresent (k : Keys) : ∃ l : Label, (member l).supportPiece A = k.val := by
    obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp k.property
    have h := hTEligible p hp
    cases p with
    | inl V =>
      obtain ⟨a, ha⟩ := h
      exact ⟨.inl a, (congrArg HypergraphPiece.oneEdge ha).trans hEq⟩
    | inr V =>
      obtain ⟨c, hc⟩ := h
      exact ⟨.inr c, (congrArg (physicalBCarrierSupport A C.toRelStructure) hc).trans hEq⟩
  let label (k : Keys) := Classical.choose (hRepresent k)
  let m (k : Keys) := member (label k)
  have hPiece (k : Keys) : (m k).supportPiece A = k.val := Classical.choose_spec (hRepresent k)
  have hCarrier (k : Keys) : (m k).carrier = k.val.carrier :=
    (ABMember.supportPiece_carrier A (m k)).symm.trans
      (congrArg HypergraphPiece.carrier (hPiece k))
  have hLabelInj : Function.Injective label := by
    intro i j hij
    apply Subtype.ext
    exact (hPiece i).symm.trans ((congrArg (fun l => (member l).supportPiece A) hij).trans (hPiece j))
  have hSupported (c : DesignatedCopy B D C family) (x : X)
      (hx : VertexSupportedInDesignated A c x) : VertexSupportedInBCopy A c.embedding x := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨c.embedding.comp a, ha, by rintro _ ⟨b, rfl⟩; exact ⟨a b, rfl⟩⟩
  have hMixed (p r : Label) (hne : p ≠ r) (x : X)
      (hp : x ∈ (member p).carrier) (hr : x ∈ (member r).carrier) :
      (member p).BIncidentSupport A x ∧ (member r).BIncidentSupport A x := by
    cases p with
    | inl a =>
      cases r with
      | inl b => exact ⟨trivial, trivial⟩
      | inr c => exact ⟨trivial, hSupported c x (hShared.1 c a x hr hp)⟩
    | inr c =>
      cases r with
      | inl a => exact ⟨hSupported c x (hShared.1 c a x hp hr), trivial⟩
      | inr d =>
        have hcd : c ≠ d := fun h => hne (congrArg Sum.inr h)
        obtain ⟨hc, hd⟩ := hShared.2 c d hcd x hp hr
        exact ⟨hSupported c x hc, hSupported d x hd⟩
  have hMixedKeys : PairwiseSharedVerticesSupportedInBMembers A m := by
    intro i j hij x hi hj
    exact hMixed (label i) (label j) (fun h => hij (hLabelInj h)) x hi hj
  have hForestKeys : ForestOfCopies (fun k : Keys => (m k).supportPiece A) := by
    simpa only [hPiece] using hForest
  obtain ⟨p, hp⟩ := hNonempty
  have : Nonempty Keys := ⟨⟨support p, Finset.mem_image.mpr ⟨p, hSub hp, rfl⟩⟩⟩
  obtain ⟨Y, R, e, hTree⟩ := mixedForest_embeds_supportedTree_of_bMemberSupport
    hForestKeys hMixedKeys alpha a₀ a₁ hne
  have liftMember (p : Set X ⊕ Set X) (hp : p ∈ T) :
      ∃ k : Keys, (m k).carrier = (support p).carrier := by
    exact ⟨⟨support p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩, hCarrier _⟩
  have downMember (k : Keys) : ∃ p ∈ T, (m k).carrier = (support p).carrier := by
    obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp k.property
    exact ⟨p, hp, (hCarrier k).trans (congrArg HypergraphPiece.carrier hEq.symm)⟩
  let inc : Embedding (physicalFamilyUnion C.toRelStructure support T)
      (mixedFamilyUnionStructure C.toRelStructure m) := {
    toFun := fun x => ⟨x.val, by
      obtain ⟨p, hp, hx⟩ := x.property
      obtain ⟨k, hk⟩ := liftMember p hp
      exact Set.mem_iUnion.mpr ⟨k, hk.symm ▸ hx⟩⟩
    injective := fun _ _ h =>
      Subtype.ext (congrArg (fun z : mixedFamilyCarrier m => z.val) h)
    map_rel_iff := fun r t => by
      change (C.toRelStructure.rel r (Subtype.val ∘ t) ∧
          ∃ k : Keys, ∀ i, (t i).val ∈ (m k).carrier) ↔
        (C.toRelStructure.rel r (Subtype.val ∘ t) ∧
          ∃ p ∈ T, ∀ i, (t i).val ∈ (support p).carrier)
      constructor
      · rintro ⟨ht, k, hk⟩
        obtain ⟨p, hp, hEq⟩ := downMember k
        exact ⟨ht, p, hp, fun i => hEq ▸ hk i⟩
      · rintro ⟨ht, p, hp, h⟩
        obtain ⟨k, hk⟩ := liftMember p hp
        exact ⟨ht, k, fun i => hk.symm ▸ h i⟩ }
  exact ⟨T, hSub, hOnly, Y, R.orderReduct, (e.comp inc).orderReduct, hTree.orderReduct⟩

/-- The empty request can start with any designated target copy and otherwise
uses the same completion. -/
theorem mixedFamilyUnion_orderReduct_of_assembledPicture
    {A : RelStructure L.withOrder UA} {B : RelStructure L.withOrder VB}
    {D : RelStructure L.withOrder P} {C : StructuralRamsey.Partite.System L.withOrder P X}
    {family : Set (Embedding B D)}
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hShared : DesignatedSharedSupport A C family)
    (q : ℕ) (hq : 1 ≤ q)
    (hComplete : ForestCompletionProperty
      (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family) q)
    (S : Finset (Set X ⊕ Set X))
    (hEligible : ∀ p ∈ S, pictureABPhysicalEligible A B D C family p)
    (hBudget : S.card ≤ q)
    (alpha : Embedding A B) (a₀ a₁ : UA) (hne : a₀ ≠ a₁) :
    ∃ T : Finset (Set X ⊕ Set X), S ⊆ T ∧
      (∀ p ∈ T, p ∈ S ∨ pictureABPhysicalDesignated B D C family p) ∧
      ∃ (Y : Type v) (R : RelStructure L Y)
        (_ : Embedding (physicalFamilyUnion C.toRelStructure.orderReduct
          (pictureABPhysicalSupport A C.toRelStructure) T) R),
        ASupportedTreeAmalgam A.orderReduct B.orderReduct Y R := by
  classical
  obtain hS | hS := S.eq_empty_or_nonempty
  · have hEmpty : (C.toRelStructure.induce (∅ : Set X)).Irreducible := by
      intro x
      exact False.elim (Set.notMem_empty x.val x.property)
    obtain ⟨c, -⟩ := hCover ∅ hEmpty
    let p : Set X ⊕ Set X := .inr (copyCarrier c.embedding)
    have hp : pictureABPhysicalDesignated B D C family p := ⟨c, rfl⟩
    have hSingleton (w) (hw : w ∈ ({p} : Finset (Set X ⊕ Set X))) :
        pictureABPhysicalEligible A B D C family w := by
      rw [Finset.mem_singleton.mp hw]
      exact ⟨c, rfl⟩
    obtain ⟨T, -, hOnly, hT⟩ := mixedFamilyUnion_orderReduct_of_nonempty_request hShared q hComplete
      {p} (Finset.singleton_nonempty p) hSingleton (by simpa using hq) alpha a₀ a₁ hne
    refine ⟨T, hS ▸ Finset.empty_subset _, ?_, hT⟩
    intro w hw
    refine Or.inr ?_
    rcases hOnly w hw with hw' | hw'
    · exact (Finset.mem_singleton.mp hw').symm ▸ hp
    · exact hw'
  · exact mixedFamilyUnion_orderReduct_of_nonempty_request hShared q hComplete
      S hS hEligible hBudget alpha a₀ a₁ hne

end StructuralRamsey.Girth
