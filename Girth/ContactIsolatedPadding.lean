import Girth.ContactCoverage

/-! Restore omitted isolated vertices after the covered hypergraph
construction. A private vertex belongs to exactly one standard.
All overlaps, actual edge labels, and mixed-forest bounds therefore
come from the old witness, and compatible finite orders extend. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J P : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

abbrev EdgeVertex := {x : V // ∃ e, x ∈ D.edgeCarrier e}

def trimIsolated : ContactHypergraphData D.EdgeVertex E PEmpty.{v+1} where
  edgeCarrier := fun e => Subtype.val ⁻¹' D.edgeCarrier e
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

theorem trimIsolated_covered (x : D.EdgeVertex) :
    ∃ e, x ∈ D.trimIsolated.edgeCarrier e := x.property

theorem trimIsolated_girth {q : ℕ} (hg : LabelledGirthGT D.edgeCarrier q) :
    LabelledGirthGT D.trimIsolated.edgeCarrier q := by
  rintro ⟨C,hC⟩
  let K : LabelledBergeCycle D.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := fun i => (C.vertex i).val
    label_injective := C.label_injective
    vertex_injective := fun i j he => C.vertex_injective (Subtype.ext he)
    left_mem := fun i => C.left_mem i
    right_mem := fun i => C.right_mem i }
  exact hg ⟨K,hC⟩

end ContactHypergraphData

namespace ContactDesignatedEmbeddings
variable {D : ContactHypergraphData V E I}
    {H : ContactHypergraphData U F J}
    {T : ContactTrainData E 1} {S : ContactTrainData F 1}
    (M : ContactDesignatedEmbeddings D.trimIsolated T H S)

/-- Glue precisely the nonisolated target vertices; all other
vertices of each restored copy are private. -/
noncomputable def isolatedGlue : J → V → Option U :=
  fun j => ContactBaseProjection.contactPartial {x : V | ∃ e, x ∈ D.edgeCarrier e} (M.emb j).vertex

theorem isolatedGlue_iff (j : J) (x : V) (u : U) :
    M.isolatedGlue j x = some u ↔
      ∃ hx : ∃ e, x ∈ D.edgeCarrier e, (M.emb j).vertex ⟨x,hx⟩ = u :=
  ContactBaseProjection.contactPartial_some_iff _ _ _ _

theorem isolatedGlue_inj (j : J) (x y : V) (u : U)
    (hx : M.isolatedGlue j x = some u) (hy : M.isolatedGlue j y = some u) :
    x = y := by
  obtain ⟨hx,hx'⟩ := (M.isolatedGlue_iff j x u).mp hx
  obtain ⟨hy,hy'⟩ := (M.isolatedGlue_iff j y u).mp hy
  exact congrArg Subtype.val ((M.emb j).vertex.injective (hx'.trans hy'.symm))

abbrev PaddedVertex := ContactGlued M.isolatedGlue

noncomputable def paddedCore : U ↪ M.PaddedVertex := contactCoreEmb M.isolatedGlue
noncomputable def paddedCopy (j : J) : V ↪ M.PaddedVertex :=
  contactStandardEmb M.isolatedGlue M.isolatedGlue_inj j

theorem paddedCopy_old (j : J) (x : D.EdgeVertex) :
    M.paddedCopy j x.val = M.paddedCore ((M.emb j).vertex x) :=
  (contactStandardEmb_eq_core M.isolatedGlue M.isolatedGlue_inj j _ _).mpr
    ((M.isolatedGlue_iff j x.val _).mpr ⟨x.property,rfl⟩)

theorem paddedCore_mem_copy (j : J) (u : U) :
    M.paddedCore u ∈ Set.range (M.paddedCopy j) ↔ u ∈ H.copyCarrier j := by
  rw [M.vertex_eq]
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (contactCoreEmb_mem_standard M.isolatedGlue M.isolatedGlue_inj j u).mp h
    obtain ⟨hx,hxu⟩ := (M.isolatedGlue_iff j x u).mp hx
    exact ⟨⟨x,hx⟩,hxu⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,M.paddedCopy_old j x⟩

noncomputable def paddedGraph : ContactHypergraphData M.PaddedVertex F J where
  edgeCarrier := fun e => M.paddedCore '' H.edgeCarrier e
  copyCarrier := fun j => Set.range (M.paddedCopy j)
  copyEdges := H.copyEdges

/-- Exact carrier equality holds also for edges of the full
target, which may have additional isolated vertices. -/
theorem padded_carrier (j : J) (e : E) :
    M.paddedGraph.edgeCarrier ((M.emb j).edge e) =
      M.paddedCopy j '' D.edgeCarrier e := by
  change M.paddedCore '' H.edgeCarrier ((M.emb j).edge e) = _
  rw [(M.emb j).carrier_eq]
  ext z
  constructor
  · rintro ⟨u,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x.val,hx,M.paddedCopy_old j x⟩
  · rintro ⟨x,hx,rfl⟩
    let y : D.EdgeVertex := ⟨x,⟨e,hx⟩⟩
    exact ⟨(M.emb j).vertex y,⟨y,hx,rfl⟩,(M.paddedCopy_old j y).symm⟩

noncomputable def paddedFamily :
    ContactDesignatedEmbeddings D T M.paddedGraph S where
  emb := fun j => {
    vertex := M.paddedCopy j
    edge := (M.emb j).edge
    carrier_eq := M.padded_carrier j
    rel_iff := (M.emb j).rel_iff
    strong := by
      intro e hn
      obtain ⟨x,⟨hx,hx'⟩,y,⟨hy,hy'⟩,hne⟩ := hn
      obtain ⟨u,hu,rfl⟩ := hx
      obtain ⟨w,hw,rfl⟩ := hy
      have hu' := (M.paddedCore_mem_copy j u).mp hx'
      have hw' := (M.paddedCore_mem_copy j w).mp hy'
      rw [M.vertex_eq] at hu' hw'
      exact (M.emb j).strong e ⟨u,⟨hu,hu'⟩,w,⟨hw,hw'⟩,
        fun he => hne (congrArg M.paddedCore he)⟩ }
  vertex_eq := fun _ => rfl
  edge_eq := M.edge_eq

theorem padded_arrow {Color : Type v} (h : M.Arrow Color) :
    M.paddedFamily.Arrow Color := h

theorem padded_girth {q : ℕ} (hg : LabelledGirthGT H.edgeCarrier q) :
    LabelledGirthGT M.paddedGraph.edgeCarrier q := by
  classical
  rintro ⟨C,hC⟩
  have hex (i : Fin C.length) : ∃ u, u ∈ H.edgeCarrier (C.label i) ∧
      M.paddedCore u = C.vertex i := C.left_mem i
  choose u hu using hex
  let K : LabelledBergeCycle H.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := u
    label_injective := C.label_injective
    vertex_injective := fun i j he => C.vertex_injective
      ((hu i).2.symm.trans ((congrArg M.paddedCore he).trans (hu j).2))
    left_mem := fun i => (hu i).1
    right_mem := by
      intro i
      obtain ⟨w,hw,he⟩ := C.right_mem i
      exact (M.paddedCore.injective (he.trans (hu i).2.symm)) ▸ hw }
  exact hg ⟨K,hC⟩

/-- On the old vertex range, every mixed piece has exactly the
image of the corresponding old carrier. -/
theorem padded_piece_trace (a : J ⊕ F) :
    M.paddedGraph.bottomCut.carrier a ∩ Set.range M.paddedCore =
      M.paddedCore '' H.bottomCut.carrier a := by
  cases a with
  | inl j =>
    ext z
    constructor
    · rintro ⟨hz,⟨u,rfl⟩⟩
      exact ⟨u,(M.paddedCore_mem_copy j u).mp hz,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨(M.paddedCore_mem_copy j u).mpr hu,⟨u,rfl⟩⟩
  | inr e =>
    change (M.paddedCore '' H.edgeCarrier e) ∩ Set.range M.paddedCore =
      M.paddedCore '' H.edgeCarrier e
    apply Set.inter_eq_left.mpr
    rintro z ⟨u,_,rfl⟩
    exact ⟨u,rfl⟩

/-- A shared vertex of different mixed pieces is never private. -/
theorem padded_piece_shared (a b : J ⊕ F) (hne : a ≠ b)
    (x : M.PaddedVertex)
    (hx : x ∈ M.paddedGraph.bottomCut.carrier a)
    (hy : x ∈ M.paddedGraph.bottomCut.carrier b) :
    x ∈ Set.range M.paddedCore := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      exact contactGlued_shared M.isolatedGlue M.isolatedGlue_inj i j
        (fun he => hne (congrArg Sum.inl he)) x hx hy
    | inr f =>
      obtain ⟨u,_,he⟩ := hy
      exact ⟨u,he⟩
  | inr e =>
    obtain ⟨u,_,he⟩ := hx
    exact ⟨u,he⟩

theorem padded_piece_intersection (a b : J ⊕ F) (hne : a ≠ b) :
    M.paddedGraph.bottomCut.carrier a ∩ M.paddedGraph.bottomCut.carrier b =
      M.paddedCore '' (H.bottomCut.carrier a ∩ H.bottomCut.carrier b) := by
  rw [contact_image_inter,← M.padded_piece_trace,← M.padded_piece_trace]
  ext x
  constructor
  · intro hx
    have h := M.padded_piece_shared a b hne x hx.1 hx.2
    exact ⟨⟨hx.1,h⟩,⟨hx.2,h⟩⟩
  · intro hx
    exact ⟨hx.1.1,hx.2.1⟩

theorem padded_smallForests {q : ℕ} (hf : H.bottomCut.ZeroSmallMixedForestsThrough q) :
    M.paddedGraph.bottomCut.ZeroSmallMixedForestsThrough q := by
  classical
  refine ⟨?_,?_⟩
  · intro hq a b hne
    rw [M.padded_piece_intersection a b hne]
    rcases hf.1 hq a b hne with hs | ⟨e,ha,hb,he⟩
    · exact Or.inl (contact_image_subsingleton M.paddedCore hs)
    · exact Or.inr ⟨e,ha,hb,congrArg (fun s : Set U => M.paddedCore '' s) he⟩
  · intro s hs hc
    obtain ⟨T₀⟩ := hf.2 s hs hc
    let U₀ := T₀.mapVertices M.paddedCore
    have he : (fun a : {a // a ∈ s} =>
        M.paddedGraph.bottomCut.carrier a.val ∩ Set.range M.paddedCore) =
        (fun a : {a // a ∈ s} => M.paddedCore '' H.bottomCut.carrier a.val) :=
      funext (fun a => M.padded_piece_trace a.val)
    let U₁ : ContactJoinTree (fun a : {a // a ∈ s} =>
        M.paddedGraph.bottomCut.carrier a.val ∩ Set.range M.paddedCore) := he.symm ▸ U₀
    refine ⟨U₁.restoreOutside ?_⟩
    intro x hx a ha b hb
    by_contra hn
    exact hx (M.padded_piece_shared a.val b.val
      (fun he => hn (Subtype.ext he)) x ha hb)

theorem padded_copy_injective (hi : Function.Injective H.copyCarrier) :
    Function.Injective M.paddedGraph.copyCarrier := by
  intro i j he
  apply hi
  ext x
  change x ∈ H.copyCarrier i ↔ x ∈ H.copyCarrier j
  rw [← M.paddedCore_mem_copy i,← M.paddedCore_mem_copy j]
  change M.paddedCore x ∈ M.paddedGraph.copyCarrier i ↔
    M.paddedCore x ∈ M.paddedGraph.copyCarrier j
  rw [he]

theorem padded_vertexCoverage (hc : ∀ x : U, ∃ j, x ∈ H.copyCarrier j)
    (x : M.PaddedVertex) : ∃ j, x ∈ M.paddedGraph.copyCarrier j := by
  rcases contactGlued_cover M.isolatedGlue M.isolatedGlue_inj x with ⟨u,rfl⟩ | ⟨j,hj⟩
  · obtain ⟨j,hj⟩ := hc u
    exact ⟨j,(M.paddedCore_mem_copy j u).mpr hj⟩
  · exact ⟨j,hj⟩

theorem padded_finite [Finite U] [Finite V] [Finite J] : Finite M.PaddedVertex :=
  Finite.of_injective (fun x : M.PaddedVertex => (x.val : U ⊕ (J × V))) Subtype.val_injective

end ContactDesignatedEmbeddings

end StructuralRamsey.Girth
