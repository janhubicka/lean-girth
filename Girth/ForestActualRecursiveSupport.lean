import Girth.ForestRelationalABCompletion
import Girth.ForestDesignatedBSupportTransport
import Girth.ForestCanonicalMixedForestTransport
import Girth.ForestOneEdgeOwnerLocalTest
import Girth.ForestMultiEdgeSupport

/-!
# Relational local witnesses supply the actual recursive support data

The direct forest increment is formulated for strong support embeddings.
An actual local train witness instead gives relational embeddings with
A-strong images. This module constructs the former from the latter and
identifies their complete support pieces. The construction takes place in
the full local core, including A-edges outside all designated local copies.

The true active source is covered by its A-support by definition. No
irreducible-in-B coverage or pruning assumption is needed for this fact.
The mixed forest transport below applies the local finite-set invariant
to physical pieces and then transports it through the core embedding.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA X Y Z I P : Type v}

private theorem recursiveSupportPiece_ext
    {F G : HypergraphPiece Z}
    (hc : F.carrier = G.carrier) (he : F.edges = G.edges) : F = G := by
  cases F
  cases G
  dsimp at hc he
  cases hc
  cases he
  rfl

/-- An A-strong relational copy induces a strong embedding of the exact
source and target A-support hypergraphs. -/
noncomputable def strongASupportEmbedding
    (A : RelStructure L UA) {B : RelStructure L X} {C : RelStructure L Y}
    (f : Embedding B C) (hStrong : AStrong A C (copyCarrier f)) :
    StrongSupportEmbedding (supportCopies A B) (supportCopies A C) where
  toFun := f
  injective := f.injective
  map_edge := by
    rintro e ⟨a, rfl⟩
    exact ⟨copyCarrier (f.comp a), ⟨f.comp a, rfl⟩,
      copyCarrier_comp_eq_image f a⟩
  reflect_edge := by
    rintro e ⟨a, rfl⟩ hMeet
    have hSub : copyCarrier a ⊆ copyCarrier f := hStrong a hMeet
    have hFactor : ∀ u : UA, ∃ x : X, a u = f x := by
      intro u
      obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
      exact ⟨x, hx.symm⟩
    let aOld := a.factorThroughRange f hFactor
    have hEq : a = f.comp aOld := by
      apply Embedding.ext
      intro u
      exact Classical.choose_spec (hFactor u)
    refine ⟨copyCarrier aOld, ⟨aOld, rfl⟩, ?_⟩
    rw [hEq]
    exact copyCarrier_comp_eq_image f aOld

/-- The support piece of this strong support embedding is the complete
relational A-support of its image, not a selected subhypergraph. -/
theorem strongASupportEmbedding_piece
    (A : RelStructure L UA) {B : RelStructure L X} {C : RelStructure L Y}
    (f : Embedding B C) (hStrong : AStrong A C (copyCarrier f)) :
    (strongASupportEmbedding A f hStrong).supportPiece = bSupportPiece A f := by
  classical
  apply recursiveSupportPiece_ext
  · rfl
  · ext e
    constructor
    · rintro ⟨eOld, ⟨a, rfl⟩, rfl⟩
      refine ⟨f.comp a, copyCarrier_comp_eq_image f a, ?_⟩
      rintro z ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    · rintro ⟨a, ha, hSub⟩
      have hFactor : ∀ u : UA, ∃ x : X, a u = f x := by
        intro u
        obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
        exact ⟨x, hx.symm⟩
      let aOld := a.factorThroughRange f hFactor
      have hEq : a = f.comp aOld := by
        apply Embedding.ext
        intro u
        exact Classical.choose_spec (hFactor u)
      refine ⟨copyCarrier aOld, ⟨aOld, rfl⟩, ?_⟩
      rw [← ha, hEq]
      exact copyCarrier_comp_eq_image f aOld

/-- Transport a strong relational local copy into the actual core image.
Only A-strongness inside the local core is used: no strongness of a
union of standard copies is assumed. -/
noncomputable def mappedStrongASupportEmbedding
    (A : RelStructure L UA)
    {B : RelStructure L X} {C : RelStructure L Y} {D : RelStructure L Z}
    (f : Embedding B C) (hStrong : AStrong A C (copyCarrier f))
    (core : Embedding C D) :
    StrongSupportEmbedding (supportCopies A B)
      (mappedSupportCopies A C D core) where
  toFun := core.comp f
  injective := (core.comp f).injective
  map_edge := by
    rintro e ⟨a, rfl⟩
    refine ⟨copyCarrier (core.comp (f.comp a)), ⟨f.comp a, rfl⟩, ?_⟩
    exact copyCarrier_comp_eq_image (core.comp f) a
  reflect_edge := by
    rintro e ⟨a, rfl⟩ hMeet
    have hOldMeet : ¬ (copyCarrier a ∩ copyCarrier f).Subsingleton := by
      intro hs
      apply hMeet
      rintro x ⟨⟨u, rfl⟩, ⟨b, hb⟩⟩ y ⟨⟨v, rfl⟩, ⟨c, hc⟩⟩
      apply congrArg core
      exact hs ⟨⟨u, rfl⟩, ⟨b, core.injective hb⟩⟩
        ⟨⟨v, rfl⟩, ⟨c, core.injective hc⟩⟩
    have hSub := hStrong a hOldMeet
    have hFactor : ∀ u : UA, ∃ x : X, a u = f x := by
      intro u
      obtain ⟨x, hx⟩ := hSub ⟨u, rfl⟩
      exact ⟨x, hx.symm⟩
    let aOld := a.factorThroughRange f hFactor
    have hEq : a = f.comp aOld := by
      apply Embedding.ext
      intro u
      exact Classical.choose_spec (hFactor u)
    refine ⟨copyCarrier aOld, ⟨aOld, rfl⟩, ?_⟩
    rw [hEq]
    exact copyCarrier_comp_eq_image (core.comp f) aOld

/-- Exact carrier-and-edge identification after mapping the local copy
through the core embedding. -/
theorem mappedStrongASupportEmbedding_piece
    (A : RelStructure L UA)
    {B : RelStructure L X} {C : RelStructure L Y} {D : RelStructure L Z}
    (f : Embedding B C) (hStrong : AStrong A C (copyCarrier f))
    (core : Embedding C D) :
    (mappedStrongASupportEmbedding A f hStrong core).supportPiece =
      (bSupportPiece A f).map core.toFunctionEmbedding := by
  classical
  rw [← strongASupportEmbedding_piece A f hStrong]
  apply recursiveSupportPiece_ext
  · exact copyCarrier_comp_eq_image core f
  · ext e
    constructor
    · rintro ⟨eOld, heOld, rfl⟩
      refine ⟨f '' eOld, ⟨eOld, heOld, rfl⟩, ?_⟩
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    · rintro ⟨eCore, ⟨eOld, heOld, rfl⟩, rfl⟩
      refine ⟨eOld, heOld, ?_⟩
      ext z
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

/-- Every true active vertex lies in an A-support edge of the induced
active source. This is independent of any designated-copy coverage. -/
theorem actualRecursiveActiveSupport_cover
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (e : UA ↪ P) :
    ∀ x : activeCarrier A C e,
      ∃ h : Set (activeCarrier A C e),
        h ∈ supportCopies A (C.induce (activeCarrier A C e)).toRelStructure ∧
          x ∈ h := by
  intro x
  rcases x.2 with ⟨a, u, hu⟩
  let aS := activeInduceProjected A a (projected_mem_activeCarrier A C e a)
  refine ⟨copyCarrier aS.val, ⟨aS.val, rfl⟩, u, ?_⟩
  exact Subtype.ext hu

/-- A nonempty true active source has a nonempty A-support family. -/
theorem actualRecursiveActiveSupport_nonempty
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (e : UA ↪ P) (hActive : (activeCarrier A C e).Nonempty) :
    (supportCopies A (C.induce (activeCarrier A C e)).toRelStructure).Nonempty := by
  obtain ⟨x, hx⟩ := hActive
  obtain ⟨h, hh, _⟩ := actualRecursiveActiveSupport_cover A C e ⟨x, hx⟩
  exact ⟨h, hh⟩

/-- The local mixed invariant tests all designated relational support
pieces and every ambient A-edge, even if no designated copy covers it. -/
def RelationalMixedSupportTest
    (A : RelStructure L UA) {B : RelStructure L X} {C : RelStructure L Y}
    (f : I → Embedding B C) (T : HypergraphPiece Y) : Prop :=
  (∃ i, T = bSupportPiece A (f i)) ∨
    ∃ a : Embedding A C, T = HypergraphPiece.oneEdge (copyCarrier a)

/-- The cutoff-two predecessor forest has at most one member, hence its
local forest obligation needs no local Ramsey or girth assumption. -/
theorem actualRecursiveLocalForest_one
    (F : I → HypergraphPiece Z) : LocalForestThrough F 1 := by
  intro Q inst idx hCard
  haveI : Subsingleton Q := Fintype.card_le_one_iff_subsingleton.mp hCard
  exact forestOfCopies_of_subsingleton (fun q => F (idx q))

/-- Injective vertex transport preserves distinctions between complete
physical support pieces. Both the carrier and all edges are used. -/
theorem actualRecursiveSupport_map_injective (core : Y ↪ Z) :
    Function.Injective (fun T : HypergraphPiece Y => T.map core) := by
  intro F G hEq
  apply recursiveSupportPiece_ext
  · have hCarrier := congrArg HypergraphPiece.carrier hEq
    change core '' F.carrier = core '' G.carrier at hCarrier
    exact (Set.image_injective.mpr core.injective) hCarrier
  · have hEdges := congrArg HypergraphPiece.edges hEq
    ext e
    constructor
    · intro he
      have hImage : core '' e ∈ (G.map core).edges := by
        rw [← hEdges]
        exact ⟨e, he, rfl⟩
      obtain ⟨eOld, heOld, hImageEq⟩ := hImage
      have hOldEq : e = eOld := (Set.image_injective.mpr core.injective) hImageEq
      simpa [hOldEq] using heOld
    · intro he
      have hImage : core '' e ∈ (F.map core).edges := by
        rw [hEdges]
        exact ⟨e, he, rfl⟩
      obtain ⟨eOld, heOld, hImageEq⟩ := hImage
      have hOldEq : e = eOld := (Set.image_injective.mpr core.injective) hImageEq
      simpa [hOldEq] using heOld

/-- An honest local mixed finite-set forest bound supplies the labelled
previous-cutoff forest used by the actual increment. The physical
copy-injectivity premise is about complete support pieces; it can be
obtained by choosing one representative before attachment. -/
theorem actualRecursiveMixedLocalForest
    (A : RelStructure L UA)
    {B : RelStructure L X} {C : RelStructure L Y} {D : RelStructure L Z}
    (f : I → Embedding B C)
    (hStrong : ∀ i, AStrong A C (copyCarrier (f i)))
    (core : Embedding C D)
    (hCopies : Function.Injective (fun i => bSupportPiece A (f i)))
    (e₀ e₁ : Set X) (he₀ : e₀ ∈ supportCopies A B)
    (he₁ : e₁ ∈ supportCopies A B) (hne : e₀ ≠ e₁)
    (m : ℕ)
    (hLocal : FiniteMixedForestThrough (RelationalMixedSupportTest A f) m) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun i => (mappedStrongASupportEmbedding A (f i) (hStrong i) core).supportPiece)
        (fun ce : {ce : Set Z // ce ∈ mappedSupportCopies A C D core} => ce.1)) m := by
  classical
  let small := fun i =>
    (mappedStrongASupportEmbedding A (f i) (hStrong i) core).supportPiece
  let tested := TransportedPiece (RelationalMixedSupportTest A f) core.toFunctionEmbedding
  have hSmall (i : I) : small i = (bSupportPiece A (f i)).map core.toFunctionEmbedding :=
    mappedStrongASupportEmbedding_piece A (f i) (hStrong i) core
  have hSmallInj : Function.Injective small := by
    intro i j hEq
    apply hCopies
    apply actualRecursiveSupport_map_injective core.toFunctionEmbedding
    simpa only [hSmall] using hEq
  apply localForestThrough_mixedOwners_of_finiteMixed
    small (fun ce : {ce : Set Z // ce ∈ mappedSupportCopies A C D core} => ce.1)
    hSmallInj Subtype.val_injective
    (fun i => StrongSupportEmbedding.supportPiece_notIsOneEdge_of_twoSourceEdges
      (mappedStrongASupportEmbedding A (f i) (hStrong i) core) e₀ e₁ he₀ he₁ hne)
    tested m
  · intro i
    exact ⟨bSupportPiece A (f i), Or.inl ⟨i, rfl⟩, hSmall i⟩
  · intro ce
    obtain ⟨a, ha⟩ := ce.2
    refine ⟨HypergraphPiece.oneEdge (copyCarrier a), Or.inr ⟨a, rfl⟩, ?_⟩
    rw [ha, HypergraphPiece.oneEdge_map, copyCarrier_comp_eq_image]
  · exact hLocal.canonicalTransport
      (RelationalMixedSupportTest A f) core.toFunctionEmbedding m

end StructuralRamsey.Girth
