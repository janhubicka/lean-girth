import Girth.ContactCanonicalFilling

/-! Embeddings of the underlying labelled trains. The ambient
copy labels do not enter the embedding. Exact carrier equality,
reflection of every train cut, and the usual two-point strong
inducedness condition are the concrete properties used throughout
the recursive construction. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J X L K : Type v}

/-- An embedding of trains before putting the part orders back.
No Ramsey, girth, or forest conclusion is assumed. -/
structure ContactTrainEmbedding {m : ℕ}
    (D : ContactHypergraphData V E I) (T : ContactTrainData E m)
    (H : ContactHypergraphData U F J) (S : ContactTrainData F m) where
  vertex : V ↪ U
  edge : E ↪ F
  carrier_eq : ∀ e, H.edgeCarrier (edge e) = vertex '' D.edgeCarrier e
  rel_iff : ∀ μ e f, S.parent μ (edge e) = S.parent μ (edge f) ↔
    T.parent μ e = T.parent μ f
  strong : ∀ f, (H.edgeCarrier f ∩ Set.range vertex).Nontrivial →
    f ∈ Set.range edge

namespace ContactTrainEmbedding
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactTrainEmbedding D T H S)

theorem mem_edge_image (e : E) (x : V) :
    M.vertex x ∈ H.edgeCarrier (M.edge e) ↔ x ∈ D.edgeCarrier e := by
  rw [M.carrier_eq]
  constructor
  · rintro ⟨y,hy,he⟩
    exact M.vertex.injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem vertex_range_of_edge (e : E) :
    H.edgeCarrier (M.edge e) ⊆ Set.range M.vertex := by
  rw [M.carrier_eq]
  rintro x ⟨y,_,rfl⟩
  exact ⟨y,rfl⟩

/-- Embeddings compose, including strong inducedness. -/
def comp {W G O : Type v}
    {K : ContactHypergraphData W G O} {R : ContactTrainData G m}
    (N : ContactTrainEmbedding H S K R) :
    ContactTrainEmbedding D T K R where
  vertex := M.vertex.trans N.vertex
  edge := M.edge.trans N.edge
  carrier_eq := by
    intro e
    change K.edgeCarrier (N.edge (M.edge e)) = _
    rw [N.carrier_eq,M.carrier_eq,Set.image_image] <;> rfl
  rel_iff := fun μ e f => (N.rel_iff μ (M.edge e) (M.edge f)).trans (M.rel_iff μ e f)
  strong := by
    intro g hn
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    obtain ⟨u,hu⟩ := hx.2
    obtain ⟨w,hw⟩ := hy.2
    have hxN : x ∈ Set.range N.vertex := ⟨M.vertex u,hu⟩
    have hyN : y ∈ Set.range N.vertex := ⟨M.vertex w,hw⟩
    obtain ⟨f,rfl⟩ := N.strong g ⟨x,⟨hx.1,hxN⟩,y,⟨hy.1,hyN⟩,hxy⟩
    have hu' : M.vertex u ∈ H.edgeCarrier f := (N.mem_edge_image f _).mp (hu.symm ▸ hx.1)
    have hw' : M.vertex w ∈ H.edgeCarrier f := (N.mem_edge_image f _).mp (hw.symm ▸ hy.1)
    have hne : M.vertex u ≠ M.vertex w := by
      intro he
      exact hxy (hu.symm.trans ((congrArg N.vertex he).trans hw))
    obtain ⟨e,he⟩ := M.strong f
      ⟨M.vertex u,⟨hu',⟨u,rfl⟩⟩,M.vertex w,⟨hw',⟨w,rfl⟩⟩,hne⟩
    exact ⟨e,congrArg N.edge he⟩

/-- The edge map of a filled train embedding keeps the template
label. The required placement compatibility is exactly the
uniqueness of the ordered partite bijection used in the paper. -/
def filledEdge : E × L ↪ F × L where
  toFun p := (M.edge p.1,p.2)
  inj' := by
    intro a b h
    exact Prod.ext (M.edge.injective (congrArg (fun p : F × L => p.1) h))
      (congrArg (fun p : F × L => p.2) h)

noncomputable def fill {Z : ContactHypergraphData X L K}
    (A : ContactFilling D Z) (B : ContactFilling H Z)
    (hplace : ∀ e x, B.place (M.edge e) x = M.vertex (A.place e x)) :
    ContactTrainEmbedding A.output (A.fillTrain T) B.output (B.fillTrain S) where
  vertex := M.vertex
  edge := M.filledEdge
  carrier_eq := by
    intro p
    change B.place (M.edge p.1) '' Z.edgeCarrier p.2 =
      M.vertex '' (A.place p.1 '' Z.edgeCarrier p.2)
    rw [Set.image_image]
    have he : (B.place (M.edge p.1) : X → U) =
        (fun x => M.vertex (A.place p.1 x)) := funext (hplace p.1)
    rw [he]
  rel_iff := by
    intro μ e f
    refine Fin.cases ?_ (fun ν => ?_) μ
    · change M.filledEdge e = M.filledEdge f ↔ e = f
      exact ⟨fun he => M.filledEdge.injective he,fun he => congrArg M.filledEdge he⟩
    · change S.parent ν (M.edge e.1) = S.parent ν (M.edge f.1) ↔
        T.parent ν e.1 = T.parent ν f.1
      exact M.rel_iff ν e.1 f.1
  strong := by
    intro p hn
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    obtain ⟨e,he⟩ := M.strong p.1
      ⟨x,⟨B.output_contained p hx.1,hx.2⟩,
        y,⟨B.output_contained p hy.1,hy.2⟩,hxy⟩
    exact ⟨(e,p.2),Prod.ext he rfl⟩

end ContactTrainEmbedding

/-- A designated copy family with actual embeddings. Ranges,
rather than only carrier sets, specify the selected edge labels. -/
structure ContactDesignatedEmbeddings {m : ℕ}
    (D : ContactHypergraphData V E I) (T : ContactTrainData E m)
    (H : ContactHypergraphData U F J) (S : ContactTrainData F m) where
  emb : J → ContactTrainEmbedding D T H S
  vertex_eq : ∀ j, H.copyCarrier j = Set.range (emb j).vertex
  edge_eq : ∀ j, H.copyEdges j = Set.range (emb j).edge

namespace ContactDesignatedEmbeddings
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings D T H S)

def Arrow (C : Type v) : Prop :=
  ∀ χ : F → C, ∃ j : J, ∃ c : C, ∀ e : E, χ ((M.emb j).edge e) = c

/-- The actual filled designated embeddings. -/
noncomputable def fill {Z : ContactHypergraphData X L K}
    (A : ContactFilling D Z) (B : ContactFilling H Z)
    (hplace : ∀ j e x, B.place ((M.emb j).edge e) x =
      (M.emb j).vertex (A.place e x)) :
    ContactDesignatedEmbeddings A.output (A.fillTrain T) B.output (B.fillTrain S) where
  emb := fun j => (M.emb j).fill A B (hplace j)
  vertex_eq := M.vertex_eq
  edge_eq := by
    intro j
    change Prod.fst ⁻¹' H.copyEdges j = Set.range (M.emb j).filledEdge
    rw [M.edge_eq]
    ext p
    constructor
    · rintro ⟨e,he⟩
      exact ⟨(e,p.2),Prod.ext he rfl⟩
    · rintro ⟨e,he⟩
      exact ⟨e.1,congrArg Prod.fst he⟩

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
