import Girth.ContactPictureStrong

/-! Contact cliques of the actual picture.  Shared points contract to
the core; wagon incidence is reflected using the bridge-pullback lemma.
This isolates the inducedness and covered-triangle reflection argument
from the proof about weighted cycles. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F J R V₀ E₀ I₀ P₀ : Type v}

namespace ContactCarrierEmbedding
variable {D : OrderOneData V E I P} {H : OrderOneData U F J R}
    (M : ContactCarrierEmbedding D H)

def contactMap : V ⊕ P → U ⊕ R :=
  Sum.map M.vertex M.wagon

theorem contactMap_injective : Function.Injective M.contactMap := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      exact congrArg Sum.inl (M.vertex.injective (Sum.inl.inj h))
    | inr p => cases h
  | inr p =>
    cases b with
    | inl x => cases h
    | inr q =>
      exact congrArg Sum.inr (M.wagon.injective (Sum.inr.inj h))

theorem real_in_range_contactMap (x : U) :
    Sum.inl x ∈ Set.range M.contactMap ↔ x ∈ Set.range M.vertex := by
  constructor
  · rintro ⟨z,h⟩
    cases z with
    | inl y => exact ⟨y,Sum.inl.inj h⟩
    | inr p => cases h
  · rintro ⟨y,hy⟩
    exact ⟨Sum.inl y,congrArg Sum.inl hy⟩

theorem wagon_in_range_contactMap (r : R) :
    Sum.inr r ∈ Set.range M.contactMap ↔ r ∈ Set.range M.wagon := by
  constructor
  · rintro ⟨z,h⟩
    cases z with
    | inl y => cases h
    | inr p => exact ⟨p,Sum.inr.inj h⟩
  · rintro ⟨p,hp⟩
    exact ⟨Sum.inr p,congrArg Sum.inr hp⟩

theorem wagon_clique_preserve (p : P) {z : V ⊕ P}
    (hz : z ∈ D.contactWagonClique p) :
    M.contactMap z ∈ H.contactWagonClique (M.wagon p) := by
  cases z with
  | inl x => exact M.wagon_vertex_preserve p x hz
  | inr q => exact congrArg M.wagon (show q = p from hz)

end ContactCarrierEmbedding

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F J R} (A : ContactPictureData D L H)

def contactDomain (i : I) : Set (U ⊕ R) := Set.range (A.std i).contactMap

theorem core_contact_in_standard (i : I) (z : V ⊕ P) :
    A.core.contactMap z ∈ A.contactDomain i ↔ z ∈ D.contactCopyClique i := by
  cases z with
  | inl x =>
    change Sum.inl (A.core.vertex x) ∈ Set.range (A.std i).contactMap ↔
      x ∈ D.copyCarrier i
    exact ((A.std i).real_in_range_contactMap _).trans (A.std_core_vertex i x)
  | inr p =>
    change Sum.inr (A.core.wagon p) ∈ Set.range (A.std i).contactMap ↔
      D.contactMeets i p
    exact ((A.std i).wagon_in_range_contactMap _).trans (A.std_core_wagon i p)

theorem shared_contact_in_core (i j : I) (hne : i ≠ j) (z : U ⊕ R)
    (hi : z ∈ A.contactDomain i) (hj : z ∈ A.contactDomain j) :
    ∃ t : V ⊕ P, A.core.contactMap t = z ∧
      t ∈ D.contactCopyClique i ∧ t ∈ D.contactCopyClique j := by
  have hcore : z ∈ Set.range A.core.contactMap := by
    cases z with
    | inl x =>
      exact (A.core.real_in_range_contactMap x).mpr
        (A.shared_vertex i j hne x (((A.std i).real_in_range_contactMap x).mp hi)
          (((A.std j).real_in_range_contactMap x).mp hj))
    | inr r =>
      exact (A.core.wagon_in_range_contactMap r).mpr
        (A.shared_wagon i j hne r (((A.std i).wagon_in_range_contactMap r).mp hi)
          (((A.std j).wagon_in_range_contactMap r).mp hj))
  obtain ⟨t,rfl⟩ := hcore
  exact ⟨t,rfl,(A.core_contact_in_standard i t).mp hi,
    (A.core_contact_in_standard j t).mp hj⟩

/-- Exact reflection of a wagon clique on a standard domain. -/
theorem standard_wagon_clique_iff (h1 : D.ContactG1) (h2 : D.ContactG2)
    (i : I) (p : P₀) (z : V₀ ⊕ P₀) :
    (A.std i).contactMap z ∈ H.contactWagonClique ((A.std i).wagon p) ↔
      z ∈ L.contactWagonClique p := by
  constructor
  · intro hz
    cases z with
    | inl x => exact A.standard_wagon_reflect h1 h2 i p x hz
    | inr q => exact (A.std i).wagon.injective (show (A.std i).wagon q =
        (A.std i).wagon p from hz)
  · exact (A.std i).wagon_clique_preserve p

/-- A wagon clique with two points in a standard domain must be a
wagon met by that standard. At a positive cut this is the two-point
wagon lemma; at the bottom cut it is strong inducedness. -/
theorem wagon_met_of_contact_pair
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (i : I) (r : R) (z t : V₀ ⊕ P₀) (hne : z ≠ t)
    (hz : (A.std i).contactMap z ∈ H.contactWagonClique r)
    (ht : (A.std i).contactMap t ∈ H.contactWagonClique r) :
    A.meets i r := by
  cases z with
  | inr p => exact ⟨p,show (A.std i).wagon p = r from hz⟩
  | inl x =>
    cases t with
    | inr p => exact ⟨p,show (A.std i).wagon p = r from ht⟩
    | inl y =>
      exact htwo i r ((A.std i).vertex x) ((A.std i).vertex y)
        (fun he => hne (congrArg Sum.inl ((A.std i).vertex.injective he)))
        ⟨x,rfl⟩ ⟨y,rfl⟩ hz ht

end ContactPictureData

/-- Designated copies of the output are exactly the lifted old copies.
These equalities are definitional for ContactTaggedPicture.output. -/
structure ContactPictureCopies
    {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H) where
  vertices : ∀ i a, H.copyCarrier (i,a) = (A.std i).vertex '' L.copyCarrier a
  edges : ∀ i a, H.copyEdges (i,a) = (A.std i).edge '' L.copyEdges a

namespace ContactPictureCopies

variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

theorem real_copy_iff (i : I) (a : I₀) (x : V₀) :
    (A.std i).vertex x ∈ H.copyCarrier (i,a) ↔ x ∈ L.copyCarrier a := by
  rw [C.vertices]
  constructor
  · rintro ⟨y,hy,he⟩
    simpa only [(A.std i).vertex.injective he] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem edge_copy_iff (i : I) (a : I₀) (e : E₀) :
    (A.std i).edge e ∈ H.copyEdges (i,a) ↔ e ∈ L.copyEdges a := by
  rw [C.edges]
  constructor
  · rintro ⟨f,hf,he⟩
    simpa only [(A.std i).edge.injective he] using hf
  · intro he
    exact ⟨e,he,rfl⟩

theorem wagon_meets_iff (i : I) (a : I₀) (p : P₀) :
    H.contactMeets (i,a) ((A.std i).wagon p) ↔ L.contactMeets a p := by
  constructor
  · rintro ⟨e,he,hp⟩
    rw [C.edges] at he
    obtain ⟨f,hf,rfl⟩ := he
    exact ⟨f,hf,(A.std i).wagon.injective (((A.std i).parent_eq f).symm.trans hp)⟩
  · rintro ⟨f,hf,hp⟩
    exact ⟨(A.std i).edge f,(C.edge_copy_iff i a f).mpr hf,
      ((A.std i).parent_eq f).trans (congrArg (A.std i).wagon hp)⟩

theorem copy_clique_iff (i : I) (a : I₀) (z : V₀ ⊕ P₀) :
    (A.std i).contactMap z ∈ H.contactCopyClique (i,a) ↔
      z ∈ L.contactCopyClique a := by
  cases z with
  | inl x => exact C.real_copy_iff i a x
  | inr p => exact C.wagon_meets_iff i a p

theorem copy_clique_in_domain (i : I) (a : I₀) {z : U ⊕ R}
    (hz : z ∈ H.contactCopyClique (i,a)) : z ∈ A.contactDomain i := by
  cases z with
  | inl x =>
    change x ∈ H.copyCarrier (i,a) at hz
    rw [C.vertices] at hz
    obtain ⟨y,hy,he⟩ := hz
    exact ⟨Sum.inl y,congrArg Sum.inl he⟩
  | inr r =>
    obtain ⟨e,he,hp⟩ := hz
    rw [C.edges] at he
    obtain ⟨f,hf,rfl⟩ := he
    exact ⟨Sum.inr (L.parent f),congrArg Sum.inr (((A.std i).parent_eq f).symm.trans hp)⟩

/-- The intersection of an external copy clique with the standard
domain contracts into the two old core-copy cliques. -/
theorem external_copy_contact (i j : I) (hne : i ≠ j) (a : I₀)
    (z : V₀ ⊕ P₀) (hz : (A.std i).contactMap z ∈ H.contactCopyClique (j,a)) :
    ∃ t, A.core.contactMap t = (A.std i).contactMap z ∧
      t ∈ D.contactCopyClique i ∧ t ∈ D.contactCopyClique j :=
  A.shared_contact_in_core i j hne _ ⟨z,rfl⟩ (C.copy_clique_in_domain j a hz)

/-- The entire intersection of an output generating clique with a
standard contact domain is contained in one local generating clique,
provided that intersection contains two distinct points. -/
theorem trace_clique (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (i : I) (b : (I × I₀) ⊕ R)
    (x y : V₀ ⊕ P₀) (hne : x ≠ y)
    (hx : (A.std i).contactMap x ∈ H.contactClique b)
    (hy : (A.std i).contactMap y ∈ H.contactClique b) :
    ∃ a : I₀ ⊕ P₀, ∀ z, (A.std i).contactMap z ∈ H.contactClique b →
      z ∈ L.contactClique a := by
  classical
  cases b with
  | inr r =>
    obtain ⟨p,rfl⟩ := A.wagon_met_of_contact_pair htwo i r x y hne hx hy
    exact ⟨Sum.inr p,fun z hz => (A.standard_wagon_clique_iff h1 h2 i p z).mp hz⟩
  | inl b =>
    obtain ⟨j,b⟩ := b
    by_cases hij : i = j
    · subst j
      exact ⟨Sum.inl b,fun z hz => (C.copy_clique_iff i b z).mp hz⟩
    · obtain ⟨u,hu,hui,huj⟩ := C.external_copy_contact i j hij b x hx
      obtain ⟨v,hv,hvi,hvj⟩ := C.external_copy_contact i j hij b y hy
      have huv : u ≠ v := by
        intro he
        apply hne
        exact (A.std i).contactMap_injective (hu.symm.trans ((congrArg A.core.contactMap he).trans hv))
      obtain ⟨p,hp⟩ := h2 i j hij ⟨u,⟨hui,huj⟩,v,⟨hvi,hvj⟩,huv⟩
      have hW : ∀ z, (A.std i).contactMap z ∈ H.contactCopyClique (j,b) →
          (A.std i).contactMap z ∈ H.contactWagonClique (A.core.wagon p) := by
        intro z hz
        obtain ⟨t,ht,hti,htj⟩ := C.external_copy_contact i j hij b z hz
        rw [← ht]
        exact A.core.wagon_clique_preserve p (hp ⟨hti,htj⟩)
      obtain ⟨q,hq⟩ := A.wagon_met_of_contact_pair htwo i (A.core.wagon p) x y hne
        (hW x hx) (hW y hy)
      refine ⟨Sum.inr q,?_⟩
      intro z hz
      apply (A.standard_wagon_clique_iff h1 h2 i q z).mp
      rw [hq]
      exact hW z hz

/-- The standard contact graph is induced, and every covered triangle
is reflected. This pair formulation also proves reflection for larger
cliques whose vertices are in a standard. -/
theorem reflect_adjacency (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (i : I) {x y : V₀ ⊕ P₀}
    (h : contactAdjacent H.contactClique ((A.std i).contactMap x) ((A.std i).contactMap y)) :
    contactAdjacent L.contactClique x y := by
  obtain ⟨hne,b,hx,hy⟩ := h
  have hxy : x ≠ y := fun he => hne (congrArg (A.std i).contactMap he)
  obtain ⟨a,ha⟩ := C.trace_clique h1 h2 htwo i b x y hxy hx hy
  exact ⟨hxy,a,ha x hx,ha y hy⟩

theorem preserve_adjacency (i : I) {x y : V₀ ⊕ P₀}
    (h : contactAdjacent L.contactClique x y) :
    contactAdjacent H.contactClique ((A.std i).contactMap x) ((A.std i).contactMap y) := by
  obtain ⟨hne,a,hx,hy⟩ := h
  have hxy := fun he => hne ((A.std i).contactMap_injective he)
  cases a with
  | inl a =>
    exact ⟨hxy,Sum.inl (i,a),(C.copy_clique_iff i a x).mpr hx,
      (C.copy_clique_iff i a y).mpr hy⟩
  | inr p =>
    exact ⟨hxy,Sum.inr ((A.std i).wagon p),
      (A.std i).wagon_clique_preserve p hx,(A.std i).wagon_clique_preserve p hy⟩

end ContactPictureCopies

namespace ContactTaggedPicture
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    (T : ContactTaggedPicture D L)

def pictureCopies : ContactPictureCopies T.toPictureData where
  vertices := fun _ _ => rfl
  edges := fun _ _ => rfl

end ContactTaggedPicture
end StructuralRamsey.Girth
