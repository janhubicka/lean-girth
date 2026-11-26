import Girth.ContactPartPreservation
import Girth.ContactImageDedup

/-! Restrict to the union of the actual designated copies.
Only unused edges and vertices are deleted; the mixed family is
reindexed by a genuine injection, rather than deleting nodes from
an already chosen join tree. This works at every forest cutoff. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

abbrev UsedVertex := {x : V // ∃ i, x ∈ D.copyCarrier i}
abbrev UsedEdge := {e : E // ∃ i, e ∈ D.copyEdges i}

def usedVertexEmb : D.UsedVertex ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
def usedEdgeEmb : D.UsedEdge ↪ E := ⟨Subtype.val,Subtype.val_injective⟩

def usedGraph : ContactHypergraphData D.UsedVertex D.UsedEdge I where
  edgeCarrier := fun e => D.usedVertexEmb ⁻¹' D.edgeCarrier e.val
  copyCarrier := fun i => D.usedVertexEmb ⁻¹' D.copyCarrier i
  copyEdges := fun i => D.usedEdgeEmb ⁻¹' D.copyEdges i

theorem usedGraph_vertexCoverage (x : D.UsedVertex) :
    ∃ i, x ∈ D.usedGraph.copyCarrier i := x.property

theorem usedGraph_edgeCoverage (e : D.UsedEdge) :
    ∃ i, e ∈ D.usedGraph.copyEdges i := e.property

theorem usedGraph_copyCarrier_injective
    (h : Function.Injective D.copyCarrier) :
    Function.Injective D.usedGraph.copyCarrier := by
  intro i j he
  apply h
  ext x
  constructor
  · intro hx
    let z : D.UsedVertex := ⟨x,⟨i,hx⟩⟩
    have hz : z ∈ D.usedGraph.copyCarrier i := hx
    rw [he] at hz
    exact hz
  · intro hx
    let z : D.UsedVertex := ⟨x,⟨j,hx⟩⟩
    have hz : z ∈ D.usedGraph.copyCarrier j := hx
    rw [← he] at hz
    exact hz

/-- Preserve the literal edge labels and lift every labelled Berge cycle. -/
theorem usedGraph_girth {q : ℕ} (h : LabelledGirthGT D.edgeCarrier q) :
    LabelledGirthGT D.usedGraph.edgeCarrier q := by
  rintro ⟨C,hC⟩
  let K : LabelledBergeCycle D.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := fun i => (C.label i).val
    vertex := fun i => (C.vertex i).val
    label_injective := fun i j he => C.label_injective (Subtype.ext he)
    vertex_injective := fun i j he => C.vertex_injective (Subtype.ext he)
    left_mem := fun i => C.left_mem i
    right_mem := fun i => C.right_mem i }
  exact h ⟨K,hC⟩

/-- Each selected mixed piece has exactly its old index. -/
def usedPiece : I ⊕ D.UsedEdge ↪ I ⊕ E where
  toFun := Sum.map id Subtype.val
  inj' := by
    intro a b h
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr f => cases h
    | inr e =>
      cases b with
      | inl j => cases h
      | inr f => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

theorem usedPiece_carrier (a : I ⊕ D.UsedEdge) :
    D.usedGraph.bottomCut.carrier a =
      D.usedVertexEmb ⁻¹' D.bottomCut.carrier (D.usedPiece a) := by
  cases a <;> rfl

theorem usedPiece_edges_mem (a : I ⊕ D.UsedEdge) (e : D.UsedEdge) :
    e ∈ D.usedGraph.bottomCut.edges a ↔ e.val ∈ D.bottomCut.edges (D.usedPiece a) := by
  cases a with
  | inl i => rfl
  | inr f =>
    change e = f ↔ e.val = f.val
    exact ⟨congrArg Subtype.val,Subtype.ext⟩

theorem usedPiece_edge_survives (a : I ⊕ D.UsedEdge) {e : E}
    (he : e ∈ D.bottomCut.edges (D.usedPiece a)) :
    ∃ i, e ∈ D.copyEdges i := by
  cases a with
  | inl i => exact ⟨i,he⟩
  | inr f =>
    change e = f.val at he
    rw [he]
    exact f.property

theorem usedGraph_pairwise (h : D.bottomCut.ZeroPairwise) :
    D.usedGraph.bottomCut.ZeroPairwise := by
  intro a b hne
  rcases h (D.usedPiece a) (D.usedPiece b)
      (fun he => hne (D.usedPiece.injective he)) with hs | ⟨e,ha,hb,he⟩
  · left
    intro x hx y hy
    rw [D.usedPiece_carrier,D.usedPiece_carrier] at hx hy
    exact Subtype.ext (hs hx hy)
  · right
    let f : D.UsedEdge := ⟨e,D.usedPiece_edge_survives a ha⟩
    refine ⟨f,(D.usedPiece_edges_mem a f).mpr ha,
      (D.usedPiece_edges_mem b f).mpr hb,?_⟩
    rw [D.usedPiece_carrier,D.usedPiece_carrier]
    exact congrArg (fun A : Set V => D.usedVertexEmb ⁻¹' A) he

/-- Pull a join tree back along the vertex inclusion and reindex
the mixed pieces. The occurrence subtree of each surviving vertex
is exactly its old occurrence subtree. -/
theorem usedGraph_smallForests {q : ℕ} (h : D.bottomCut.ZeroSmallMixedForestsThrough q) :
    D.usedGraph.bottomCut.ZeroSmallMixedForestsThrough q := by
  classical
  refine ⟨fun hq => D.usedGraph_pairwise (h.1 hq),?_⟩
  intro s hs hc
  let t := s.image D.usedPiece
  have ht : t.Nonempty := by
    obtain ⟨a,ha⟩ := hs
    exact ⟨D.usedPiece a,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
  obtain ⟨T⟩ := h.2 t ht (Finset.card_image_le.trans hc)
  let f : {a // a ∈ s} → {b // b ∈ t} := fun a =>
    ⟨D.usedPiece a.val,Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  have hi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (D.usedPiece.injective (congrArg Subtype.val he))
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp b.property
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  let r := Equiv.ofBijective f ⟨hi,hsurj⟩
  let U := T.reindex r
  have heq : ∀ x : D.UsedVertex,
      {i : {a // a ∈ s} | x ∈ D.usedGraph.bottomCut.carrier i.val} =
      {i : {a // a ∈ s} | x.val ∈ D.bottomCut.carrier (D.usedPiece i.val)} := by
    intro x
    ext a
    change (x ∈ D.usedGraph.bottomCut.carrier a.val) ↔ _
    rw [D.usedPiece_carrier]
    rfl
  refine ⟨{ tree := U.tree, isTree := U.isTree, running := ?_ }⟩
  intro x
  rw [heq x]
  exact U.running x.val

end ContactHypergraphData

namespace ContactDesignatedEmbeddings
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings D T H S)

def usedVertex (j : J) : V ↪ H.UsedVertex where
  toFun x := ⟨(M.emb j).vertex x,⟨j,by rw [M.vertex_eq]; exact ⟨x,rfl⟩⟩⟩
  inj' := fun _ _ he => (M.emb j).vertex.injective (congrArg Subtype.val he)

def usedEdge (j : J) : E ↪ H.UsedEdge where
  toFun e := ⟨(M.emb j).edge e,⟨j,by rw [M.edge_eq]; exact ⟨e,rfl⟩⟩⟩
  inj' := fun _ _ he => (M.emb j).edge.injective (congrArg Subtype.val he)

/-- The restriction really contains the entire image of each
old train embedding. The cut equivalences survive on the retained
labels and no new strongly induced edge obligation is introduced. -/
def restrictCovered :
    ContactDesignatedEmbeddings D T H.usedGraph (S.pullTrain H.usedEdgeEmb) where
  emb := fun j => {
    vertex := M.usedVertex j
    edge := M.usedEdge j
    carrier_eq := by
      intro e
      ext x
      change (x.val ∈ H.edgeCarrier ((M.emb j).edge e)) ↔
        x ∈ (M.usedVertex j) '' D.edgeCarrier e
      rw [(M.emb j).carrier_eq]
      constructor
      · rintro ⟨y,hy,he⟩
        exact ⟨y,hy,Subtype.ext he⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y,hy,rfl⟩
    rel_iff := fun μ e f =>
      (S.pullTrain_rel H.usedEdgeEmb μ (M.usedEdge j e) (M.usedEdge j f)).trans
        ((M.emb j).rel_iff μ e f)
    strong := by
      intro e hn
      obtain ⟨x,hx,y,hy,hxy⟩ := hn
      have hx' : x.val ∈ Set.range (M.emb j).vertex := by
        obtain ⟨u,hu⟩ := hx.2
        exact ⟨u,congrArg Subtype.val hu⟩
      have hy' : y.val ∈ Set.range (M.emb j).vertex := by
        obtain ⟨u,hu⟩ := hy.2
        exact ⟨u,congrArg Subtype.val hu⟩
      obtain ⟨f,hf⟩ := (M.emb j).strong e.val
        ⟨x.val,⟨hx.1,hx'⟩,y.val,⟨hy.1,hy'⟩,fun he => hxy (Subtype.ext he)⟩
      exact ⟨f,Subtype.ext hf⟩ }
  vertex_eq := by
    intro j
    ext x
    change x.val ∈ H.copyCarrier j ↔ x ∈ Set.range (M.usedVertex j)
    rw [M.vertex_eq]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨u,Subtype.ext hu⟩
    · rintro ⟨u,rfl⟩
      exact ⟨u,rfl⟩
  edge_eq := by
    intro j
    ext e
    change e.val ∈ H.copyEdges j ↔ e ∈ Set.range (M.usedEdge j)
    rw [M.edge_eq]
    constructor
    · rintro ⟨f,hf⟩
      exact ⟨f,Subtype.ext hf⟩
    · rintro ⟨f,rfl⟩
      exact ⟨f,rfl⟩

theorem restrictCovered_arrow {Color : Type v} [Nonempty Color] (h : M.Arrow Color) :
    M.restrictCovered.Arrow Color := by
  classical
  intro χ
  let χ' : F → Color := fun e =>
    if he : ∃ j, e ∈ H.copyEdges j then χ ⟨e,he⟩
    else Classical.choice (inferInstance : Nonempty Color)
  obtain ⟨j,c,hj⟩ := h χ'
  refine ⟨j,c,?_⟩
  intro e
  have he : ∃ j', (M.emb j).edge e ∈ H.copyEdges j' := (M.usedEdge j e).property
  have h' := hj e
  change χ (M.usedEdge j e) = c
  simpa only [χ',dif_pos he] using h'

/-- If the target is covered by its edges, the restriction is
also covered by edges, not just by designated copies. -/
theorem restrictCovered_noIsolated (hc : ∀ x, ∃ e, x ∈ D.edgeCarrier e) :
    ∀ x : H.UsedVertex, ∃ e : H.UsedEdge, x ∈ H.usedGraph.edgeCarrier e := by
  intro x
  obtain ⟨j,hj⟩ := x.property
  rw [M.vertex_eq] at hj
  obtain ⟨v,hv⟩ := hj
  obtain ⟨e,he⟩ := hc v
  refine ⟨M.usedEdge j e,?_⟩
  change x.val ∈ H.edgeCarrier ((M.emb j).edge e)
  rw [(M.emb j).carrier_eq]
  exact ⟨v,he,hv⟩

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
