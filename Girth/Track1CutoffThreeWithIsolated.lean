import Girth.DecorationPartiteBridge
import Girth.ForestOneEdgeOwnerLocalTest
import Girth.ForestStar
import Girth.Track1OrderedCutoffThree
import Girth.Track1IsolatedRestoration

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure TrainRecursiveWitness IsolatedRestoration

universe v w
variable {U V : Type v}

/-- The full ordered cutoff-three witness for a finite partite hypergraph
with at least two distinct edges. Isolated vertices are allowed in the
target. The set of witness vertices is precisely the union of the
selected copies. -/
theorem cutoffThree_withIsolated
    [LinearOrder U] [Finite U] [Nonempty U] [LinearOrder V] [Finite V]
    (H : Set (Set V)) (sourcePart : V → U)
    (hTrans : EdgeTransversal H sourcePart)
    (hBlocks : ∀ x y : V, sourcePart x < sourcePart y → x < y)
    (hGirth : GirthGT H 3)
    (hTwo : ∃ e ∈ H, ∃ e' ∈ H, e ≠ e')
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (vertices : Set W)
      (K : Set (Set W)) (part : W → U)
      (family : Set (StrongSupportEmbedding H K)),
      EdgeTransversal K part ∧ StrongSupportCoversEdges H K family ∧ GirthGT K 3 ∧
      (∀ x, x ∈ vertices ↔ ∃ f ∈ family, x ∈ Set.range f) ∧
      (∀ e ∈ K, e ⊆ vertices) ∧
      (∀ f ∈ family, ∀ x, part (f x) = sourcePart x) ∧
      (∀ f ∈ family, ∀ x y : V, x < y → @LT.lt W o.toLT (f x) (f y)) ∧
      FiniteMixedForestThrough (fun P =>
        (∃ f ∈ family, P = f.supportPiece) ∨
        (∃ e ∈ K, P = HypergraphPiece.oneEdge e)) 3 ∧
      StrongSupportEdgeArrow H family κ := by
  classical
  let S : Set V := {x | ∃ e ∈ H, x ∈ e}
  let edges₀ := inducedSupport S H
  let part₀ : S → U := sourcePart ∘ Subtype.val
  have hSupport (e : Set V) (he : e ∈ H) : e ⊆ S := fun x hx => ⟨e, he, hx⟩
  have hRestore (e : Set V) (he : e ∈ H) :
      Subtype.val '' (Subtype.val ⁻¹' e : Set S) = e := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hSupport e he hx⟩, hx, rfl⟩
  obtain ⟨e₁, he₁, e₂, he₂, hNe⟩ := hTwo
  have hTwo₀ : ∃ e ∈ edges₀, ∃ e' ∈ edges₀, e ≠ e' := by
    refine ⟨_, ⟨e₁, he₁, rfl⟩, _, ⟨e₂, he₂, rfl⟩, ?_⟩
    intro h
    apply hNe
    exact (hRestore e₁ he₁).symm.trans
      ((congrArg (Set.image Subtype.val) h).trans (hRestore e₂ he₂))
  have hGirth₀ : GirthGT edges₀ 3 := by
    apply girthGT_three_of_edgeProjection (Subtype.val : S → V) _ _ _ hGirth
    · intro e he
      obtain ⟨e', he', rfl⟩ := he
      rwa [hRestore e' he']
    · exact (Set.image_injective.mpr Subtype.val_injective).injOn
    · intro e _
      exact Subtype.val_injective.injOn
  have hNonempty₀ : edges₀.Nonempty := ⟨_, ⟨e₁, he₁, rfl⟩⟩
  have hCovered₀ (x : S) : ∃ e ∈ edges₀, x ∈ e := by
    obtain ⟨e, he, hx⟩ := x.2
    exact ⟨_, ⟨e, he, rfl⟩, hx⟩
  have hTrans₀ : EdgeTransversal edges₀ part₀ := by
    rintro _ ⟨e, he, rfl⟩ p
    obtain ⟨x, hx, hUnique⟩ := hTrans e he p
    refine ⟨⟨x, hSupport e he hx.1⟩, hx, ?_⟩
    exact fun y hy => Subtype.ext (hUnique y.1 hy)
  let L : RelLanguage.{0} := ⟨PEmpty, PEmpty.elim⟩
  let A₀ : RelStructure L U := ⟨fun p => PEmpty.elim p⟩
  let A := A₀.ordered
  let Target := decorateSupportSystem A edges₀ part₀ hTrans₀
  have hA : A.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hPartite :=
    decorateSupportSystem_isPartiteOver A hA hTrans₀ hGirth₀ hNonempty₀ hCovered₀
  have hExact : supportCopies A Target.toRelStructure = edges₀ :=
    (decorateSupport_exact A hA hTrans₀ hGirth₀ hNonempty₀ hCovered₀).1
  let edgeEmbedding {e : Set S} (he : e ∈ edges₀) : Embedding A Target.toRelStructure :=
    decorateSupport_edgeEmbedding A hTrans₀ he
  have hCarrier {e : Set S} (he : e ∈ edges₀) : copyCarrier (edgeEmbedding he) = e :=
    decorateSupport_edgeCarrier A hTrans₀ he
  have hGenerated : AGenerated A Target.toRelStructure := by
    constructor
    · intro x
      obtain ⟨e, he, hx⟩ := hCovered₀ x
      exact ⟨edgeEmbedding he, (hCarrier he).symm ▸ hx⟩
    · intro r x h
      obtain ⟨e, he, hIn⟩ := decorateSupport_relationsCovered A edges₀ part₀ r x h
      exact ⟨edgeEmbedding he, fun j => (hCarrier he).symm ▸ hIn j⟩
  have hDifferent : ∃ a b : Embedding A Target.toRelStructure, ¬ SameCopy a b := by
    obtain ⟨e, he, e', he', hd⟩ := hTwo₀
    exact ⟨edgeEmbedding he, edgeEmbedding he', fun h =>
      hd ((hCarrier he).symm.trans (h.trans (hCarrier he')))⟩
  have hGirthTarget : GirthGT (supportCopies A Target.toRelStructure) 3 := by
    rwa [hExact]
  have hMono (a : Embedding A Target.toRelStructure) : StrictMono a := by
    intro x y hxy
    have hPos := relationalA_embedding_preserves_parts_of_rigid A Target hA hPartite
      (orderedA_self_embedding_is_id A₀) a
    apply hBlocks
    change Target.part (a x) < Target.part (a y)
    rw [hPos x, hPos y]
    exact hxy
  have hWitness := cutoffThree_orderedCoveredSupportWitness
    A₀ Target hPartite hGenerated hDifferent hGirthTarget hMono κ
  change ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (vertices : Set W)
    (K : Set (Set W)) (part : W → U)
    (family : Set (StrongSupportEmbedding (supportCopies A Target.toRelStructure) K)), _ at hWitness
  rw [hExact] at hWitness
  obtain ⟨W, hW, o, _, K, oldPart, family, hK, hCover, hG, _, _, hPart, hOrder, hForest, hArrow⟩ :=
    hWitness
  letI : Finite W := hW
  letI : LinearOrder W := o
  let I := Selection S H K family
  haveI : Finite I := by
    apply Finite.of_injective (fun i : I => i.1.toFun)
    intro i j h
    apply Subtype.ext
    rcases i with ⟨⟨f, _, _, _⟩, _⟩
    rcases j with ⟨⟨g, _, _, _⟩, _⟩
    change f = g at h
    cases h
    rfl
  let iFin := Fintype.ofFinite I
  let eFin := @Fintype.equivFin I iFin
  letI : LinearOrder I := LinearOrder.lift' eFin eFin.injective
  haveI : Nonempty W := by
    obtain ⟨f, _, _⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    obtain ⟨x, hx, _⟩ := hTrans e₁ he₁ (Classical.choice (inferInstance : Nonempty U))
    exact ⟨f ⟨x, hSupport e₁ he₁ hx.1⟩⟩
  let v := Vertex S H K family
  let K' := edges S H K family
  let F := Set.range (strongLift S H K family hSupport)
  let vertices := {x : v | ∃ f ∈ F, x ∈ Set.range f}
  obtain ⟨o', _, hOrder'⟩ := exists_order S H K family (fun i : I => hOrder i.1 i.2)
  obtain ⟨hCover', hArrow'⟩ := covered_and_arrow S H K family hSupport hCover hArrow
  refine ⟨v, inferInstance, o', vertices, K', part S H K family sourcePart oldPart, F,
    edgeTransversal S H K family sourcePart oldPart hK, hCover',
    girth_three S H K family hG, (fun _ => Iff.rfl), ?_, ?_, ?_, ?_, hArrow'⟩
  · intro e he x hx
    obtain ⟨f, hf, e₀, _, rfl⟩ := hCover' e he
    obtain ⟨y, _, rfl⟩ := hx
    exact ⟨f, hf, ⟨y, rfl⟩⟩
  · rintro _ ⟨i, rfl⟩ x
    exact strongLift_preserves_parts S H K family hSupport sourcePart oldPart
      (fun j z => hPart j.1 j.2 z) i x
  · rintro _ ⟨i, rfl⟩ x y hxy
    exact hOrder' i x y hxy
  · apply FiniteMixedForestThrough.of_tested_subset _ _ 3 ?_
      (mixedForest S H K family hSupport (fun i : I => hOrder i.1 i.2) hTwo₀ 3 hForest)
    rintro Q (⟨_, ⟨i, rfl⟩, hQ⟩ | hEdge)
    · exact Or.inl ⟨i, hQ⟩
    · exact Or.inr hEdge

private theorem oneEdgeWithCentre_mixedForest
    {H : Set (Set V)} (f : StrongSupportEmbedding H H)
    (e : Set V) (he : e ∈ f.supportPiece.edges) (hOnly : ∀ e' ∈ H, e' = e) :
    FiniteMixedForestThrough
      (fun P => (∃ f' ∈ ({f} : Set (StrongSupportEmbedding H H)), P = f'.supportPiece) ∨
        (∃ e' ∈ H, P = HypergraphPiece.oneEdge e')) 3 := by
  classical
  intro s hTest _
  let I := {P : HypergraphPiece V // P ∈ s}
  have hKinds (i : I) :
      i.1 = f.supportPiece ∨ i.1 = HypergraphPiece.oneEdge e := by
    rcases hTest i.1 i.2 with ⟨f', h, hi⟩ | ⟨e', he', hi⟩
    · exact Or.inl (hi.trans (congrArg StrongSupportEmbedding.supportPiece
        (Set.mem_singleton_iff.mp h)))
    · exact Or.inr (hi.trans (congrArg HypergraphPiece.oneEdge (hOnly e' he')))
  by_cases hCentre : f.supportPiece ∈ s
  · let c : I := ⟨f.supportPiece, hCentre⟩
    let J := {i : I // i ≠ c}
    have hLeaf (j : J) : j.1.1 = HypergraphPiece.oneEdge e := by
      rcases hKinds j.1 with h | h
      · exact (j.2 (Subtype.ext h)).elim
      · exact h
    have hPair : ∀ ⦃j k : J⦄, j ≠ k → (e ∩ e).Subsingleton := by
      intro j k hjk
      exact (hjk (Subtype.ext (Subtype.ext ((hLeaf j).trans (hLeaf k).symm)))).elim
    have hStar := forest_centerWithEdgeLeaves f.supportPiece (fun _ : J => e)
      (fun _ => he) hPair
    let equiv : Option J ≃ I := Equiv.optionSubtypeNe c
    have hReindexed : ForestOfCopies (fun i : Option J => (equiv i).1) := by
      convert hStar using 1
      funext i
      cases i with
      | none => rfl
      | some j => exact hLeaf j
    simpa only [Equiv.apply_symm_apply] using hReindexed.reindex equiv.symm
  · have hLeaf (i : I) : i.1 = HypergraphPiece.oneEdge e :=
      (hKinds i).resolve_left (fun h => hCentre (h ▸ i.2))
    letI : Subsingleton I :=
      ⟨fun i j => Subtype.ext ((hLeaf i).trans (hLeaf j).symm)⟩
    exact forestOfCopies_of_subsingleton (fun i : I => i.1)

/-- The ordered local-forest partite lemma at cutoff three, including
the one-edge case and private restoration of isolated target vertices. -/
theorem cutoffThree_orderedForestPartite
    [LinearOrder U] [Finite U] [Nonempty U] [LinearOrder V] [Finite V]
    (H : Set (Set V)) (sourcePart : V → U)
    (hTrans : EdgeTransversal H sourcePart)
    (hBlocks : ∀ x y : V, sourcePart x < sourcePart y → x < y)
    (hGirth : GirthGT H 3) (hNonempty : H.Nonempty)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (vertices : Set W)
      (K : Set (Set W)) (part : W → U)
      (family : Set (StrongSupportEmbedding H K)),
      EdgeTransversal K part ∧ StrongSupportCoversEdges H K family ∧ GirthGT K 3 ∧
      (∀ x, x ∈ vertices ↔ ∃ f ∈ family, x ∈ Set.range f) ∧
      (∀ e ∈ K, e ⊆ vertices) ∧
      (∀ f ∈ family, ∀ x, part (f x) = sourcePart x) ∧
      (∀ f ∈ family, ∀ x y : V, x < y → @LT.lt W o.toLT (f x) (f y)) ∧
      FiniteMixedForestThrough (fun P =>
        (∃ f ∈ family, P = f.supportPiece) ∨
        (∃ e ∈ K, P = HypergraphPiece.oneEdge e)) 3 ∧
      StrongSupportEdgeArrow H family κ := by
  by_cases hTwo : ∃ e ∈ H, ∃ e' ∈ H, e ≠ e'
  · exact cutoffThree_withIsolated H sourcePart hTrans hBlocks hGirth hTwo κ
  obtain ⟨e, he⟩ := hNonempty
  have hOnly (e' : Set V) (he' : e' ∈ H) : e' = e := by
    by_contra h
    exact hTwo ⟨e', he', e, he, h⟩
  let f : StrongSupportEmbedding H H :=
    ⟨id, Function.injective_id, fun e' he' => ⟨e', he', (Set.image_id _).symm⟩,
      fun e' he' _ => ⟨e', he', (Set.image_id _).symm⟩⟩
  have hId (e' : Set V) : f '' e' = e' := Set.image_id e'
  have hSupport : e ∈ f.supportPiece.edges := ⟨e, he, (hId e).symm⟩
  refine ⟨V, inferInstance, inferInstance, Set.univ, H, sourcePart, {f},
    hTrans, ?_, hGirth, ?_, (fun _ _ => Set.subset_univ _), ?_, ?_,
    oneEdgeWithCentre_mixedForest f e hSupport hOnly, ?_⟩
  · intro e' he'
    exact ⟨f, Set.mem_singleton _, e', he', (hId e').symm⟩
  · intro x
    exact ⟨fun _ => ⟨f, Set.mem_singleton _, x, rfl⟩, fun _ => Set.mem_univ _⟩
  · intro f' hf x
    cases Set.mem_singleton_iff.mp hf
    rfl
  · intro f' hf x y hxy
    cases Set.mem_singleton_iff.mp hf
    exact hxy
  · intro χ
    refine ⟨f, Set.mem_singleton _, χ ⟨e, he⟩, fun e' he' => ?_⟩
    apply congrArg χ
    exact Subtype.ext ((hId e').trans (hOnly e' he'))

/-- In the usual partite formulation only the orders inside individual
parts are prescribed. Sorting the input and output part blocks makes the
global auxiliary orders without changing any inside-part comparison. -/
theorem cutoffThree_forestPartite
    [orderU : LinearOrder U] [Finite U] [Nonempty U] [orderV : LinearOrder V] [Finite V]
    (H : Set (Set V)) (sourcePart : V → U)
    (hTrans : EdgeTransversal H sourcePart)
    (hGirth : GirthGT H 3) (hNonempty : H.Nonempty)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W) (vertices : Set W)
      (K : Set (Set W)) (part : W → U)
      (family : Set (StrongSupportEmbedding H K)),
      EdgeTransversal K part ∧ StrongSupportCoversEdges H K family ∧ GirthGT K 3 ∧
      (∀ x, x ∈ vertices ↔ ∃ f ∈ family, x ∈ Set.range f) ∧
      (∀ e ∈ K, e ⊆ vertices) ∧
      (∀ f ∈ family, ∀ x, part (f x) = sourcePart x) ∧
      (∀ x y : W, part x < part y → @LT.lt W o.toLT x y) ∧
      (∀ f ∈ family, ∀ x y : V, sourcePart x = sourcePart y → x < y →
        @LT.lt W o.toLT (f x) (f y)) ∧
      FiniteMixedForestThrough (fun P =>
        (∃ f ∈ family, P = f.supportPiece) ∨
        (∃ e ∈ K, P = HypergraphPiece.oneEdge e)) 3 ∧
      StrongSupportEdgeArrow H family κ := by
  let inputKey (x : V) : U ×ₗ V := toLex (sourcePart x, x)
  let inputOrder : LinearOrder V :=
    LinearOrder.lift' inputKey (fun _ _ h => congrArg (fun k => (ofLex k).2) h)
  have inputLt (x y : V) : @LT.lt V inputOrder.toLT x y ↔
      sourcePart x < sourcePart y ∨ sourcePart x = sourcePart y ∧ @LT.lt V orderV.toLT x y :=
    @Prod.Lex.toLex_lt_toLex U V orderU.toLT orderV.toLT _ _
  have hInputBlocks (x y : V) (h : sourcePart x < sourcePart y) :
      @LT.lt V inputOrder.toLT x y := (inputLt x y).mpr (Or.inl h)
  obtain ⟨W, hW, o, vertices, K, targetPart, family, hTrans', hCover, hG,
    hVertices, hEdges, hParts, hOrders, hForest, hArrow⟩ :=
    @cutoffThree_orderedForestPartite U V inferInstance inferInstance inferInstance
      inputOrder inferInstance H sourcePart hTrans hInputBlocks hGirth hNonempty κ
      ‹Fintype κ› ‹Nonempty κ›
  let : LinearOrder W := o
  let outputKey (x : W) : U ×ₗ W := toLex (targetPart x, x)
  let outputOrder : LinearOrder W :=
    LinearOrder.lift' outputKey (fun _ _ h => congrArg (fun k => (ofLex k).2) h)
  have outputLt (x y : W) : @LT.lt W outputOrder.toLT x y ↔
      targetPart x < targetPart y ∨ targetPart x = targetPart y ∧ @LT.lt W o.toLT x y :=
    @Prod.Lex.toLex_lt_toLex U W orderU.toLT o.toLT _ _
  refine ⟨W, hW, outputOrder, vertices, K, targetPart, family,
    hTrans', hCover, hG, hVertices, hEdges, hParts, ?_, ?_, hForest, hArrow⟩
  · intro x y h
    exact (outputLt x y).mpr (Or.inl h)
  · intro f hf x y hSame hxy
    have hTargetSame : targetPart (f x) = targetPart (f y) := by rw [hParts f hf, hParts f hf, hSame]
    have hInput := (inputLt x y).mpr (Or.inr ⟨hSame, hxy⟩)
    exact (outputLt (f x) (f y)).mpr (Or.inr ⟨hTargetSame, hOrders f hf x y hInput⟩)

#print axioms StructuralRamsey.Girth.cutoffThree_forestPartite
#print axioms StructuralRamsey.Girth.cutoffThree_orderedForestPartite
#print axioms StructuralRamsey.Girth.cutoffThree_withIsolated

end StructuralRamsey.Girth
