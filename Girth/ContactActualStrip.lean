import Girth.ContactTrainPullback
import Girth.ContactTrainEmbedding
import Girth.ContactProjectionPreservation

/-! The literal edge-covered active strip. Its vertices and edges
are subtypes of the old picture, and its train is the restriction
of the original train. In particular unused vertices over the
active base edge are not forced into the common amalgamation. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J X B : Type v}

namespace ContactBaseProjection
variable {L : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactBaseProjection L base)

abbrev StripVertex (b : B) := P.strip b
abbrev StripEdge (b : B) := {e : E // P.edge e = b}

def stripVertexEmb (b : B) : P.StripVertex b ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

def stripEdgeEmb (b : B) : P.StripEdge b ↪ E :=
  ⟨Subtype.val,Subtype.val_injective⟩

def stripHypergraph (b : B) :
    ContactHypergraphData (P.StripVertex b) (P.StripEdge b) PEmpty.{v+1} where
  edgeCarrier := fun e => Subtype.val ⁻¹' L.edgeCarrier e.val
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

def stripPart (b : B) (x : P.StripVertex b) : X := P.vertex x.val

theorem strip_carrier_image (b : B) (e : P.StripEdge b) :
    P.stripVertexEmb b '' (P.stripHypergraph b).edgeCarrier e =
      L.edgeCarrier e.val := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,P.edge_subset_strip e.val b e.property hx⟩,hx,rfl⟩

theorem strip_part_image (b : B) (e : P.StripEdge b) :
    P.stripPart b '' (P.stripHypergraph b).edgeCarrier e = base b := by
  have he : P.vertex '' (P.stripVertexEmb b '' (P.stripHypergraph b).edgeCarrier e) = base b := by
    rw [P.strip_carrier_image,P.edge_image,e.property]
  rw [Set.image_image] at he
  exact he

theorem strip_part_inj (b : B) (e : P.StripEdge b) :
    Set.InjOn (P.stripPart b) ((P.stripHypergraph b).edgeCarrier e) :=
  fun x hx y hy he => Subtype.ext (P.edge_inj e.val hx hy he)

theorem strip_covered (b : B) (x : P.StripVertex b) :
    ∃ e : P.StripEdge b, x ∈ (P.stripHypergraph b).edgeCarrier e := by
  obtain ⟨e,he,hx⟩ := x.property
  exact ⟨⟨e,he⟩,hx⟩

theorem strip_linear (b : B)
    (h : ∀ e f : E, e ≠ f → (L.edgeCarrier e ∩ L.edgeCarrier f).Subsingleton) :
    ∀ e f : P.StripEdge b, e ≠ f →
      ((P.stripHypergraph b).edgeCarrier e ∩ (P.stripHypergraph b).edgeCarrier f).Subsingleton := by
  intro e f hn x hx y hy
  exact Subtype.ext (h e.val f.val (fun he => hn (Subtype.ext he)) hx hy)

variable {m : ℕ} (S : ContactTrainData E m)

def stripTrain (b : B) : ContactTrainData (P.StripEdge b) m :=
  S.pullTrain (P.stripEdgeEmb b)

theorem strip_wagon_image_subset (b : B) (μ : Fin (m+1))
    (p : (P.stripTrain S b).Wagon μ) :
    P.stripVertexEmb b '' ((P.stripHypergraph b).atCut
      ((P.stripTrain S b).parent μ)).contactWagonCarrier p ⊆
        (L.atCut (S.parent μ)).contactWagonCarrier p.val := by
  rintro x ⟨y,⟨e,he,hy⟩,rfl⟩
  exact ⟨e.val,congrArg Subtype.val he,hy⟩

theorem strip_wagon_girth (b : B) (μ : Fin (m+1)) {g : ℕ}
    (hg : LabelledGirthGT (L.atCut (S.parent μ)).contactWagonCarrier g) :
    LabelledGirthGT ((P.stripHypergraph b).atCut
      ((P.stripTrain S b).parent μ)).contactWagonCarrier g := by
  rintro ⟨C,hC⟩
  let K : LabelledBergeCycle (L.atCut (S.parent μ)).contactWagonCarrier := {
    length := C.length
    hlength := C.hlength
    label := fun i => (C.label i).val
    vertex := fun i => (C.vertex i).val
    label_injective := fun i j he => C.label_injective (Subtype.ext he)
    vertex_injective := fun i j he => C.vertex_injective (Subtype.ext he)
    left_mem := fun i => P.strip_wagon_image_subset S b μ (C.label i)
      ⟨C.vertex i,C.left_mem i,rfl⟩
    right_mem := fun i => P.strip_wagon_image_subset S b μ (C.label (cyclicSucc i))
      ⟨C.vertex i,C.right_mem i,rfl⟩
  }
  exact hg ⟨K,hC⟩

theorem strip_parameter (b : B) (μ ν : Fin (m+1)) (allowed : Set V)
    (h : L.Parameter S μ ν allowed) :
    (P.stripHypergraph b).Parameter (P.stripTrain S b) μ ν
      (P.stripVertexEmb b ⁻¹' allowed) := by
  intro e f x he hx hy hn
  exact (S.pullTrain_rel (P.stripEdgeEmb b) μ e f).mpr
    (h e.val f.val x.val ((S.pullTrain_rel (P.stripEdgeEmb b) ν e f).mp he) hx hy hn)

/-- Extend a map defined on a subtype by none outside its domain.
This is the actual partial map used by tagged free union. -/
noncomputable def contactPartial {Y Z : Type v} (A : Set Y) (f : A → Z) (y : Y) : Option Z :=
  by
    classical
    exact if h : y ∈ A then some (f ⟨y,h⟩) else none

theorem contactPartial_some_iff {Y Z : Type v} (A : Set Y) (f : A → Z) (y : Y) (z : Z) :
    contactPartial A f y = some z ↔ ∃ h : y ∈ A, f ⟨y,h⟩ = z := by
  classical
  unfold contactPartial
  split_ifs with h
  · constructor
    · intro he
      exact ⟨h,Option.some.inj he⟩
    · rintro ⟨h',he⟩
      exact congrArg some he
  · constructor
    · intro he
      cases he
    · rintro ⟨h',_⟩
      exact (h h').elim

end ContactBaseProjection

namespace ContactDesignatedEmbeddings
variable {L : ContactHypergraphData V E I} {base : B → Set X}
    {P : ContactBaseProjection L base} {m : ℕ} {S : ContactTrainData E m}
    {b : B}
    {D : ContactHypergraphData U F J} {T : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings (P.stripHypergraph b) (P.stripTrain S b) D T)

noncomputable def vertexPartial (i : J) : V → Option U :=
  ContactBaseProjection.contactPartial (P.strip b) (M.emb i).vertex

noncomputable def edgePartial (i : J) : E → Option F :=
  ContactBaseProjection.contactPartial {e | P.edge e = b} (M.emb i).edge

theorem vertexPartial_iff (i : J) (x : V) (u : U) :
    M.vertexPartial i x = some u ↔
      ∃ h : x ∈ P.strip b, (M.emb i).vertex ⟨x,h⟩ = u :=
  ContactBaseProjection.contactPartial_some_iff _ _ _ _

theorem edgePartial_iff (i : J) (e : E) (f : F) :
    M.edgePartial i e = some f ↔
      ∃ h : P.edge e = b, (M.emb i).edge ⟨e,h⟩ = f :=
  ContactBaseProjection.contactPartial_some_iff _ _ _ _

theorem vertexPartial_inj (i : J) (x y : V) (a : U)
    (hx : M.vertexPartial i x = some a) (hy : M.vertexPartial i y = some a) :
    x = y := by
  obtain ⟨hx,he⟩ := (M.vertexPartial_iff i x a).mp hx
  obtain ⟨hy,hf⟩ := (M.vertexPartial_iff i y a).mp hy
  exact congrArg Subtype.val ((M.emb i).vertex.injective (he.trans hf.symm))

theorem edgePartial_inj (i : J) (e f : E) (a : F)
    (he : M.edgePartial i e = some a) (hf : M.edgePartial i f = some a) :
    e = f := by
  obtain ⟨he,h₁⟩ := (M.edgePartial_iff i e a).mp he
  obtain ⟨hf,h₂⟩ := (M.edgePartial_iff i f a).mp hf
  exact congrArg Subtype.val ((M.emb i).edge.injective (h₁.trans h₂.symm))

/-- The partial gluing maps required by ContactTrainStrip are
constructed from actual designated embeddings of the literal strip. -/
noncomputable def stripGluing (hne : Nonempty (P.StripEdge b)) :
    ContactTrainStrip D L T S where
  vertexGlue := M.vertexPartial
  edgeGlue := M.edgePartial
  vertex_inj := M.vertexPartial_inj
  edge_inj := M.edgePartial_inj
  vertex_domain := by
    intro i u
    rw [M.vertex_eq]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx,he⟩ := (M.vertexPartial_iff i x u).mp hx
      exact ⟨⟨x,hx⟩,he⟩
    · rintro ⟨x,he⟩
      exact ⟨x.val,(M.vertexPartial_iff i x.val u).mpr ⟨x.property,he⟩⟩
  edge_domain := by
    intro i f
    rw [M.edge_eq]
    constructor
    · rintro ⟨e,he⟩
      obtain ⟨he,hf⟩ := (M.edgePartial_iff i e f).mp he
      exact ⟨⟨e,he⟩,hf⟩
    · rintro ⟨e,he⟩
      exact ⟨e.val,(M.edgePartial_iff i e.val f).mpr ⟨e.property,he⟩⟩
  shared_edge_carrier := by
    intro i e f he
    obtain ⟨hb,hf⟩ := (M.edgePartial_iff i e f).mp he
    let a : P.StripEdge b := ⟨e,hb⟩
    have heq : (M.emb i).edge a = f := hf
    rw [← heq,(M.emb i).carrier_eq]
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      let y : P.StripVertex b := ⟨x,P.edge_subset_strip e b hb hx⟩
      have hy : M.vertexPartial i x = some ((M.emb i).vertex y) :=
        (M.vertexPartial_iff i x _).mpr ⟨y.property,rfl⟩
      have hg := (contactStandardEmb_eq_core M.vertexPartial M.vertexPartial_inj i x _).mpr hy
      exact ⟨(M.emb i).vertex y,⟨y,hx,rfl⟩,hg.symm⟩
    · rintro ⟨u,⟨x,hx,rfl⟩,rfl⟩
      have hg : M.vertexPartial i x.val = some ((M.emb i).vertex x) :=
        (M.vertexPartial_iff i x.val _).mpr ⟨x.property,rfl⟩
      exact ⟨x.val,hx,(contactStandardEmb_eq_core M.vertexPartial M.vertexPartial_inj i x.val _).mpr hg⟩
  shared_rel := by
    intro μ i e f u w he hf
    obtain ⟨he,hu⟩ := (M.edgePartial_iff i e u).mp he
    obtain ⟨hf,hw⟩ := (M.edgePartial_iff i f w).mp hf
    let a : P.StripEdge b := ⟨e,he⟩
    let c : P.StripEdge b := ⟨f,hf⟩
    have hu' : (M.emb i).edge a = u := hu
    have hw' : (M.emb i).edge c = w := hw
    rw [← hu',← hw']
    exact ((S.pullTrain_rel (P.stripEdgeEmb b) μ a c).symm.trans
      ((M.emb i).rel_iff μ a c).symm)
  shared_nonempty := by
    intro i
    obtain ⟨e⟩ := hne
    exact ⟨e.val,(M.emb i).edge e,(M.edgePartial_iff i e.val _).mpr ⟨e.property,rfl⟩⟩

theorem stripGluing_active (hne : Nonempty (P.StripEdge b)) :
    (M.stripGluing hne).ActiveOver P b := by
  constructor
  · intro i x
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨hx,_⟩ := (M.vertexPartial_iff i x u).mp hu
      exact hx
    · intro hx
      exact ⟨(M.emb i).vertex ⟨x,hx⟩,(M.vertexPartial_iff i x _).mpr ⟨hx,rfl⟩⟩
  · intro i e
    constructor
    · rintro ⟨f,hf⟩
      obtain ⟨he,_⟩ := (M.edgePartial_iff i e f).mp hf
      exact he
    · intro he
      exact ⟨(M.emb i).edge ⟨e,he⟩,(M.edgePartial_iff i e _).mpr ⟨he,rfl⟩⟩

/-- Part preservation of the designated strip embeddings gives
exactly the core projection compatibility, with no extra
assumption on the tagged output. -/
theorem stripGluing_coreOver (hne : Nonempty (P.StripEdge b)) (p : U → X)
    (hpart : ∀ i x, p ((M.emb i).vertex x) = P.stripPart b x)
    (himage : ∀ f, p '' D.edgeCarrier f = base b)
    (hinj : ∀ f, Set.InjOn p (D.edgeCarrier f)) :
    (M.stripGluing hne).CoreOver P b p where
  vertex_compatible := by
    intro i x y h
    obtain ⟨hx,hy⟩ := (M.vertexPartial_iff i x y).mp h
    rw [← hy]
    exact hpart i ⟨x,hx⟩
  edge_image := himage
  edge_inj := hinj

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
