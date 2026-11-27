import Girth.ContactRelationalExact
import Girth.ContactRelationalInput
import Girth.ContactOuterAssembly
import Girth.ContactLocalForestPartite

/-! Restore the original B, including isolated support vertices.
The order extension is compatible with the ORIGINAL target order,
not with a rearrangement of its one-point types. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}} {U V W E F I J : Type v}

namespace ContactHypergraphData
variable (H : ContactHypergraphData W F J)

def MixedSharedSupported : Prop :=
  ∀ i j : J ⊕ F, i ≠ j → ∀ x,
    x ∈ H.bottomCut.carrier i → x ∈ H.bottomCut.carrier j →
    (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier i) ∧
    (∃ e, x ∈ H.edgeCarrier e ∧ H.edgeCarrier e ⊆ H.bottomCut.carrier j)

/-- The edge-edge part of the global allowed-intersection
condition is precisely linearity on actual labels. -/
theorem linear_of_pairwise (h : H.bottomCut.ZeroPairwise) :
    ∀ e f, e ≠ f → (H.edgeCarrier e ∩ H.edgeCarrier f).Subsingleton := by
  intro e f hne
  rcases h (Sum.inr e) (Sum.inr f) (fun h => hne (Sum.inr.inj h)) with hs | ⟨k,he,hf,_⟩
  · exact hs
  · change k = e at he
    change k = f at hf
    exact (hne (he.symm.trans hf)).elim

end ContactHypergraphData

namespace ContactDesignatedEmbeddings
variable {D : ContactHypergraphData V E I}
    {H : ContactHypergraphData W F J}
    {T : ContactTrainData E 1} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D.trimIsolated T H S)

/-- Arbitrary copy completion survives padding, with the same
set of completion labels, not just families of bounded total size. -/
theorem padded_completable {m : ℕ} (h : ContactCompletable H.copyCarrier m) :
    ContactCompletable M.paddedGraph.copyCarrier m := by
  classical
  intro s hs hcard
  obtain ⟨t,hst,⟨T₀⟩⟩ := h s hs hcard
  let sel : {i : J // i ∈ t} ↪ J ⊕ F :=
    ⟨fun i => Sum.inl i.val,fun i j h => Subtype.ext (Sum.inl.inj h)⟩
  exact ⟨t,hst,M.padded_joinTree sel T₀⟩

/-- Every shared vertex lies in a support edge in each incident
piece. For a B-copy this uses coverage of the *source* trim,
not just coverage of the ambient core by copies. -/
theorem padded_sharedSupported : M.paddedGraph.MixedSharedSupported := by
  intro i j hne x hx hy
  obtain ⟨w,hw⟩ := M.padded_piece_shared i j hne x hx hy
  have aux (a : J ⊕ F) (ha : x ∈ M.paddedGraph.bottomCut.carrier a) :
      ∃ e, x ∈ M.paddedGraph.edgeCarrier e ∧
        M.paddedGraph.edgeCarrier e ⊆ M.paddedGraph.bottomCut.carrier a := by
    cases a with
    | inr e => exact ⟨e,ha,Set.Subset.rfl⟩
    | inl k =>
      change x ∈ Set.range (M.paddedCopy k) at ha
      rw [← hw] at ha
      have h := (M.paddedCore_mem_copy k w).mp ha
      rw [M.vertex_eq k] at h
      obtain ⟨z,hz⟩ := h
      obtain ⟨e,he⟩ := z.property
      let f := (M.emb k).edge e
      have hEq : M.paddedCopy k z.val = x :=
        (M.paddedCopy_old k z).trans ((congrArg M.paddedCore hz).trans hw)
      have hmem : x ∈ M.paddedGraph.edgeCarrier f := by
        rw [← hEq]
        exact ((M.paddedFamily.emb k).mem_edge_image e z.val).mpr he
      refine ⟨f,hmem,?_⟩
      change M.paddedGraph.edgeCarrier f ⊆ M.paddedGraph.copyCarrier k
      rw [M.paddedFamily.vertex_eq k]
      exact (M.paddedFamily.emb k).vertex_range_of_edge e
  exact ⟨aux i hx,aux j hy⟩

/-- Extend the unlabelled global order before restoring the actual
relation tuples. There is no assumption that one-point labels are
monotone in either order. -/
theorem exists_paddedOrder [Fintype V] [Fintype W] [Finite J]
    [LinearOrder V] [LinearOrder W]
    (hord : ∀ j (x y : D.EdgeVertex), x.val < y.val →
      (M.emb j).vertex x < (M.emb j).vertex y) :
    ∃ o : LinearOrder M.PaddedVertex,
      ∀ j x y, x < y → o.lt (M.paddedCopy j x) (M.paddedCopy j y) := by
  classical
  have hc : ContactGluedOrder.Compatible M.isolatedGlue := by
    intro j x y u w hx hy hxy
    obtain ⟨hx,hxu⟩ := (M.isolatedGlue_iff j x u).mp hx
    obtain ⟨hy,hyw⟩ := (M.isolatedGlue_iff j y w).mp hy
    exact hxu ▸ hyw ▸ hord j ⟨x,hx⟩ ⟨y,hy⟩ hxy
  obtain ⟨o,_,h⟩ := ContactGluedOrder.exists_order M.isolatedGlue hc M.isolatedGlue_inj
  exact ⟨o,h⟩

end ContactDesignatedEmbeddings

/-- A fully restored finite support witness, with exactly the
geometry needed by relational realization and minimum completion. -/
structure ContactRelationalSupportWitness
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] (m : ℕ) (Color : Type v) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge 1
  family : ContactDesignatedEmbeddings (contactRelationalTarget A.ordered B.ordered)
    (contactHeightOne (Embedding A.ordered B.ordered)) graph train
  order : LinearOrder Vertex
  emb_order : ∀ j x y, x < y → order.lt ((family.emb j).vertex x) ((family.emb j).vertex y)
  diagonal : ∀ i j x y, (family.emb i).vertex x = (family.emb j).vertex y →
    ContactDiagonalEq B.ordered x y
  covered : graph.CopyCovered
  pairwise : graph.bottomCut.ZeroPairwise
  completable : ContactCompletable graph.copyCarrier m
  distinct : Function.Injective graph.copyCarrier
  shared : graph.MixedSharedSupported
  arrow : family.Arrow Color

/-- The one-A-copy case uses the target itself. In particular no
duplicate designated B-images are introduced by an iteration. -/
theorem contactRelationalSupportWitness_single
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    [Subsingleton (Embedding A.ordered B.ordered)]
    (α : Embedding A.ordered B.ordered) (m : ℕ) (Color : Type v) :
    Nonempty (ContactRelationalSupportWitness A B m Color) := by
  classical
  let D := contactRelationalTarget A.ordered B.ordered
  let E := Embedding A.ordered B.ordered
  letI : Finite E := by dsimp [E]; infer_instance
  letI : Subsingleton E := by dsimp [E]; infer_instance
  let H : ContactHypergraphData V E PUnit.{v+1} := {
    edgeCarrier := D.edgeCarrier
    copyCarrier := fun _ => Set.univ
    copyEdges := fun _ => Set.univ }
  let T := contactHeightOne E
  let M : ContactDesignatedEmbeddings D T H T := {
    emb := fun _ => {
      vertex := Function.Embedding.refl V
      edge := Function.Embedding.refl E
      carrier_eq := by intro e; change D.edgeCarrier e = id '' D.edgeCarrier e; simp
      rel_iff := fun _ _ _ => Iff.rfl
      strong := fun e _ => ⟨e,rfl⟩ }
    vertex_eq := by intro i; change Set.univ = Set.range (id : V → V); simp
    edge_eq := by intro i; change Set.univ = Set.range (id : E → E); simp }
  have hpair : H.bottomCut.ZeroPairwise := by
    intro a b hn
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (hn (congrArg Sum.inl (Subsingleton.elim i j))).elim
      | inr e =>
        exact Or.inr ⟨e,Set.mem_univ _,rfl,Set.univ_inter _⟩
    | inr e =>
      cases b with
      | inl j => exact Or.inr ⟨e,rfl,Set.mem_univ _,Set.inter_univ _⟩
      | inr f => exact (hn (congrArg Sum.inr (Subsingleton.elim e f))).elim
  have hc : ContactCompletable H.copyCarrier m := by
    intro s hs _
    let K := {i : PUnit.{v+1} // i ∈ s}
    letI : Nonempty K := by obtain ⟨i,hi⟩ := hs; exact ⟨⟨i,hi⟩⟩
    letI : Subsingleton K := ⟨fun i j => Subtype.ext (Subsingleton.elim i.val j.val)⟩
    exact ⟨s,Finset.Subset.rfl,⟨ContactJoinTree.of_subsingleton _⟩⟩
  have hShared : H.MixedSharedSupported := by
    intro a b hn x hx hy
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (hn (congrArg Sum.inl (Subsingleton.elim i j))).elim
      | inr e => exact ⟨⟨e,hy,Set.subset_univ _⟩,⟨e,hy,Set.Subset.rfl⟩⟩
    | inr e =>
      cases b with
      | inl j => exact ⟨⟨e,hx,Set.Subset.rfl⟩,⟨e,hx,Set.subset_univ _⟩⟩
      | inr f => exact (hn (congrArg Sum.inr (Subsingleton.elim e f))).elim
  exact ⟨{
    Vertex := V
    Edge := E
    Copy := PUnit.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    finiteC := inferInstance
    graph := H
    train := T
    family := M
    order := inferInstance
    emb_order := fun _ _ _ h => h
    diagonal := fun _ _ x y h => by
      change x = y at h
      subst y
      exact fun _ => Iff.rfl
    covered := ⟨fun _ => ⟨PUnit.unit,Set.mem_univ _⟩,fun _ => ⟨PUnit.unit,Set.mem_univ _⟩⟩
    pairwise := hpair
    completable := hc
    distinct := fun _ _ _ => Subsingleton.elim _ _
    shared := hShared
    arrow := by
      intro χ
      exact ⟨PUnit.unit,χ α,fun e => congrArg χ (Subsingleton.elim e α)⟩ }⟩

/-- The support hypergraph outer theorem followed by private
restoration, for every finite ordered relational target. -/
theorem contactRelationalSupportWitness_exists
    (A : RelStructure L U) (B : RelStructure L V)
    [LinearOrder U] [LinearOrder V] [Fintype U] [Finite V]
    (ha : 2 ≤ Fintype.card U)
    (α : Embedding A.ordered B.ordered)
    (g m : ℕ) (hg : 2 ≤ g) (hm : 2 ≤ m)
    (hG : GirthGT (supportCopies A.ordered B.ordered) g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    Nonempty (ContactRelationalSupportWitness A B m Color) := by
  classical
  let E := Embedding A.ordered B.ordered
  letI : Finite E := by dsimp [E]; infer_instance
  by_cases hsingle : Subsingleton E
  · letI : Subsingleton E := hsingle
    exact contactRelationalSupportWitness_single A B α m Color
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsingle
  letI : Nonempty E := ⟨α⟩
  letI : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Fintype V := Fintype.ofFinite _
  let D := contactRelationalTarget A.ordered B.ordered
  letI : Finite (ContactDiagonalType B.ordered) := contactDiagonalType_finite B.ordered
  letI : LinearOrder (ContactDiagonalType B.ordered) := contactDiagonalType_order B.ordered
  letI : Finite D.EdgeVertex :=
    Finite.of_injective (fun x : D.EdgeVertex => x.val) Subtype.val_injective
  let X := contactRelationalTrimWord A B α
  have hSource := contactRelationalTarget_girth hG
  obtain ⟨W,hcov,hpair,hcomp,_⟩ := contactOrderedOuterRamsey_qualitative ha X
    D.trimIsolated_covered g m hg hm (D.trimIsolated_girth hSource) Color
  let M := W.family
  letI : Finite W.Vertex := W.finiteV
  letI : Fintype W.Vertex := Fintype.ofFinite _
  letI : Finite W.Copy := W.finiteC
  letI : LinearOrder W.Vertex := W.order
  obtain ⟨o,ho⟩ := M.exists_paddedOrder W.emb_order
  let H := M.paddedGraph
  let N := M.paddedFamily
  have hp : H.bottomCut.ZeroPairwise := M.padded_pairwise hpair
  have hlin := H.linear_of_pairwise hp
  have hsize (e : E) : (D.edgeCarrier e).Nontrivial := by
    obtain ⟨x,y,hxy⟩ := exists_pair_ne U
    exact ⟨e x,⟨x,rfl⟩,e y,⟨y,rfl⟩,fun h => hxy (e.injective h)⟩
  have hdiag (i j : W.Copy) (x y : V) (he : M.paddedCopy i x = M.paddedCopy j y) :
      ContactDiagonalEq B.ordered x y := by
    let p := contactDiagonalLabel B.ordered
    let q := M.paddedPart p W.label
    have hp₁ : q (M.paddedCopy i x) = p x := M.paddedPart_copy p W.label W.emb_label i x
    have hp₂ : q (M.paddedCopy j y) = p y := M.paddedPart_copy p W.label W.emb_label j y
    exact (contactDiagonalLabel_eq_iff B.ordered x y).mp
      (hp₁.symm.trans ((congrArg q he).trans hp₂))
  exact ⟨{
    Vertex := M.PaddedVertex
    Edge := W.Edge
    Copy := W.Copy
    finiteV := M.padded_finite
    finiteE := W.finiteE
    finiteC := W.finiteC
    graph := H
    train := W.train
    family := N
    order := o
    emb_order := ho
    diagonal := hdiag
    covered := ⟨M.padded_vertexCoverage hcov.1,hcov.2⟩
    pairwise := hp
    completable := M.padded_completable hcomp
    distinct := N.copy_injective_of_twoEdges hsize hlin hp
    shared := M.padded_sharedSupported
    arrow := M.padded_arrow W.arrow }⟩

end StructuralRamsey.Girth
