import Girth.ContactAttachmentGeometry

/-! Actual carrier maps for the free picture amalgam at one partition level.
The only inputs are the source embeddings, exact common-core restrictions,
and vertex/edge coverage. In particular neither bridge pullback nor output
wagon linearity is a field. The all-level tagged-node construction can
supply these maps independently of the contact-cycle proof. -/

namespace StructuralRamsey.Girth

universe v
variable {V E I P U F J R V₀ E₀ I₀ P₀ : Type v}

/-- A map of vertices, edges, and wagon labels preserving exact edge
carriers and the partition. Designated copies are irrelevant here. -/
structure ContactCarrierEmbedding (D : OrderOneData V E I P)
    (H : OrderOneData U F J R) where
  vertex : V ↪ U
  edge : E ↪ F
  wagon : P ↪ R
  edge_carrier : ∀ e, H.edgeCarrier (edge e) = vertex '' D.edgeCarrier e
  parent_eq : ∀ e, H.parent (edge e) = wagon (D.parent e)

namespace ContactCarrierEmbedding

variable {D : OrderOneData V E I P} {H : OrderOneData U F J R}
    (M : ContactCarrierEmbedding D H)

theorem edge_vertex_range {e : E} {x : U} (hx : x ∈ H.edgeCarrier (M.edge e)) :
    x ∈ Set.range M.vertex := by
  rw [M.edge_carrier] at hx
  obtain ⟨y,_,he⟩ := hx
  exact ⟨y,he⟩

theorem edge_vertex_reflect (e : E) (x : V)
    (hx : M.vertex x ∈ H.edgeCarrier (M.edge e)) : x ∈ D.edgeCarrier e := by
  rw [M.edge_carrier] at hx
  obtain ⟨y,hy,he⟩ := hx
  simpa only [M.vertex.injective he] using hy

theorem wagon_vertex_preserve (p : P) (x : V) (hx : x ∈ D.contactWagonCarrier p) :
    M.vertex x ∈ H.contactWagonCarrier (M.wagon p) := by
  obtain ⟨e,he,hx⟩ := hx
  refine ⟨M.edge e,?_,?_⟩
  · rw [M.parent_eq,he]
  · rw [M.edge_carrier]
    exact ⟨x,hx,rfl⟩

end ContactCarrierEmbedding

/-- The exact common-core intersection data at a fixed cut. The vertex
and edge maps are the free-amalgam maps. The wagon maps are the injective
maps on generated partition classes. The core-copy incidence conditions
say exactly which source vertices, edges and wagons survive in a standard.
The coverage clauses rule out phantom vertices, edges and wagon labels. -/
structure ContactPictureData (D : OrderOneData V E I P)
    (L : OrderOneData V₀ E₀ I₀ P₀) (H : OrderOneData U F J R) where
  core : ContactCarrierEmbedding D H
  std : I → ContactCarrierEmbedding L H
  vertex_cover : ∀ x : U, x ∈ Set.range core.vertex ∨
    ∃ i, x ∈ Set.range (std i).vertex
  edge_cover : ∀ e : F, e ∈ Set.range core.edge ∨
    ∃ i, e ∈ Set.range (std i).edge
  parent_surjective : Function.Surjective H.parent
  std_core_vertex : ∀ i x, core.vertex x ∈ Set.range (std i).vertex ↔ x ∈ D.copyCarrier i
  std_core_edge : ∀ i e, core.edge e ∈ Set.range (std i).edge ↔ e ∈ D.copyEdges i
  std_core_wagon : ∀ i p, core.wagon p ∈ Set.range (std i).wagon ↔ D.contactMeets i p
  shared_vertex : ∀ i j : I, i ≠ j → ∀ x : U,
    x ∈ Set.range (std i).vertex → x ∈ Set.range (std j).vertex → x ∈ Set.range core.vertex
  shared_wagon : ∀ i j : I, i ≠ j → ∀ r : R,
    r ∈ Set.range (std i).wagon → r ∈ Set.range (std j).wagon → r ∈ Set.range core.wagon

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F J R} (A : ContactPictureData D L H)

def standard (i : I) : Set U := Set.range (A.std i).vertex
def meets (i : I) (r : R) : Prop := r ∈ Set.range (A.std i).wagon

/-- A mixed core contact is witnessed either by a core edge or by a
standard copy whose vertex and wagon both come from the core. -/
theorem core_contact (p : P) (x : V)
    (hx : A.core.vertex x ∈ H.contactWagonCarrier (A.core.wagon p)) :
    contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p) := by
  obtain ⟨e,he,hxe⟩ := hx
  rcases A.edge_cover e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
  · have hp : D.parent f = p := A.core.wagon.injective ((A.core.parent_eq f).symm.trans he)
    have hxf := A.core.edge_vertex_reflect f x hxe
    exact ⟨(by intro hh; cases hh),Sum.inr p,⟨f,hp,hxf⟩,rfl⟩
  · have hv := (A.std_core_vertex i x).mp ((A.std i).edge_vertex_range hxe)
    have hm : D.contactMeets i p := (A.std_core_wagon i p).mp
      ⟨L.parent f,((A.std i).parent_eq f).symm.trans he⟩
    exact ⟨(by intro hh; cases hh),Sum.inl i,hv,hm⟩

/-- A core incidence in a wagon met by a standard pulls back to an
actual core edge in that standard, by G1. -/
theorem core_bridge_into_standard (h1 : D.ContactG1) (i : I) (p : P) (x : V)
    (hxi : x ∈ D.copyCarrier i) (hxp : x ∈ D.contactWagonCarrier p)
    (hm : D.contactMeets i p) :
    ∃ e : E₀, H.parent ((A.std i).edge e) = A.core.wagon p ∧
      A.core.vertex x ∈ H.edgeCarrier ((A.std i).edge e) := by
  obtain ⟨f,hf,hp,hx⟩ := h1.bridge i p (Or.inl hm) x hxi hxp
  obtain ⟨e,he⟩ := (A.std_core_edge i f).mpr hf
  refine ⟨e,?_,?_⟩
  · rw [he,A.core.parent_eq,hp]
  · rw [he,A.core.edge_carrier]
    exact ⟨x,hx,rfl⟩

/-- Lemma bridgepullback: an output wagon met by a standard contains a
standard edge through every common vertex. No output linearity is used. -/
theorem bridge_pullback (h1 : D.ContactG1) (h2 : D.ContactG2)
    (i : I) (r : R) (x : U) (hm : A.meets i r)
    (hxi : x ∈ A.standard i) (hx : x ∈ H.contactWagonCarrier r) :
    ∃ e : E₀, H.parent ((A.std i).edge e) = r ∧
      x ∈ H.edgeCarrier ((A.std i).edge e) := by
  classical
  obtain ⟨f,hf,hxf⟩ := hx
  rcases A.edge_cover f with ⟨e,rfl⟩ | ⟨j,e,rfl⟩
  · have hr : r = A.core.wagon (D.parent e) := hf.symm.trans (A.core.parent_eq e)
    rw [hr] at hm ⊢
    obtain ⟨u,rfl⟩ := A.core.edge_vertex_range hxf
    exact A.core_bridge_into_standard h1 i (D.parent e) u
      ((A.std_core_vertex i u).mp hxi)
      ⟨e,rfl,A.core.edge_vertex_reflect e u hxf⟩
      ((A.std_core_wagon i (D.parent e)).mp hm)
  · by_cases hij : i = j
    · subst j
      exact ⟨e,hf,hxf⟩
    · have hxj := (A.std j).edge_vertex_range hxf
      obtain ⟨u,rfl⟩ := A.shared_vertex i j hij x hxi hxj
      have hmj : A.meets j r := ⟨L.parent e,((A.std j).parent_eq e).symm.trans hf⟩
      obtain ⟨p,rfl⟩ := A.shared_wagon i j hij r hm hmj
      have hui := (A.std_core_vertex i u).mp hxi
      have huj := (A.std_core_vertex j u).mp hxj
      have hpi := (A.std_core_wagon i p).mp hm
      have hpj := (A.std_core_wagon j p).mp hmj
      obtain ⟨g,_,hg,hug⟩ := (D.contact_bridges_of_shared_mixed h1 h2 hij hui huj hpi hpj).1
      exact A.core_bridge_into_standard h1 i p u hui ⟨g,hg,hug⟩ hpi

/-- Exact wagon incidence on the vertex carrier of a standard. This
stronger equality is useful for contact-clique reflection as well. -/
theorem standard_wagon_reflect (h1 : D.ContactG1) (h2 : D.ContactG2)
    (i : I) (p : P₀) (x : V₀)
    (hx : (A.std i).vertex x ∈ H.contactWagonCarrier ((A.std i).wagon p)) :
    x ∈ L.contactWagonCarrier p := by
  obtain ⟨e,he,hxe⟩ := A.bridge_pullback h1 h2 i ((A.std i).wagon p)
    ((A.std i).vertex x) ⟨p,rfl⟩ ⟨x,rfl⟩ hx
  exact ⟨e,(A.std i).wagon.injective (((A.std i).parent_eq e).symm.trans he),
    (A.std i).edge_vertex_reflect e x hxe⟩

theorem standard_wagon_inter_eq (h1 : D.ContactG1) (h2 : D.ContactG2)
    (i : I) (p : P₀) :
    H.contactWagonCarrier ((A.std i).wagon p) ∩ A.standard i =
      (A.std i).vertex '' L.contactWagonCarrier p := by
  ext x
  constructor
  · rintro ⟨hx,⟨u,rfl⟩⟩
    exact ⟨u,A.standard_wagon_reflect h1 h2 i p u hx,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(A.std i).wagon_vertex_preserve p u hu,⟨u,rfl⟩⟩

/-- Local comparison of two output wagons meeting the same standard,
proved by the preceding pullback and old wagon linearity. -/
theorem local_pair (h1 : D.ContactG1) (h2 : D.ContactG2) (hL : L.ContactLinear)
    (i : I) (r s : R) (hr : A.meets i r) (hs : A.meets i s)
    (x y : U) (hxy : x ≠ y) (hxi : x ∈ A.standard i) (hyi : y ∈ A.standard i)
    (hxr : x ∈ H.contactWagonCarrier r) (hyr : y ∈ H.contactWagonCarrier r)
    (hxs : x ∈ H.contactWagonCarrier s) (hys : y ∈ H.contactWagonCarrier s) : r = s := by
  classical
  obtain ⟨p,rfl⟩ := hr
  obtain ⟨q,rfl⟩ := hs
  obtain ⟨u,rfl⟩ := hxi
  obtain ⟨v,rfl⟩ := hyi
  by_contra hn
  have hpq : p ≠ q := fun he => hn (congrArg (A.std i).wagon he)
  exact hxy (congrArg (A.std i).vertex (hL.2 p q hpq
    ⟨A.standard_wagon_reflect h1 h2 i p u hxr,A.standard_wagon_reflect h1 h2 i q u hxs⟩
    ⟨A.standard_wagon_reflect h1 h2 i p v hyr,A.standard_wagon_reflect h1 h2 i q v hys⟩))

/-- Every private vertex of a standard can be incident only to a wagon
met by that standard. -/
theorem private_vertex_meets (i : I) (r : R) (x : U)
    (hpriv : x ∉ Set.range A.core.vertex) (hxi : x ∈ A.standard i)
    (hx : x ∈ H.contactWagonCarrier r) : A.meets i r := by
  classical
  obtain ⟨e,he,hxe⟩ := hx
  rcases A.edge_cover e with ⟨f,rfl⟩ | ⟨j,f,rfl⟩
  · exact (hpriv (A.core.edge_vertex_range hxe)).elim
  · by_cases hij : i = j
    · subst j
      exact ⟨L.parent f,((A.std i).parent_eq f).symm.trans he⟩
    · exact (hpriv (A.shared_vertex i j hij x hxi ((A.std j).edge_vertex_range hxe))).elim

/-- A wagon without a core ancestor has exactly one standard owner,
and all its vertices are in that standard. -/
theorem private_wagon (r : R) (hr : r ∉ Set.range A.core.wagon) :
    ∃ i, A.meets i r ∧ H.contactWagonCarrier r ⊆ A.standard i ∧
      (∀ j, A.meets j r → j = i) := by
  classical
  obtain ⟨e,he⟩ := A.parent_surjective r
  have hm : ∃ i, A.meets i r := by
    rcases A.edge_cover e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
    · exact (hr ⟨D.parent f, (A.core.parent_eq f).symm.trans he⟩).elim
    · exact ⟨i,L.parent f,((A.std i).parent_eq f).symm.trans he⟩
  obtain ⟨i,hi⟩ := hm
  have huniq : ∀ j, A.meets j r → j = i := by
    intro j hj
    by_contra hji
    exact hr (A.shared_wagon j i hji r hj hi)
  refine ⟨i,hi,?_,huniq⟩
  rintro x ⟨f,hf,hx⟩
  rcases A.edge_cover f with ⟨g,rfl⟩ | ⟨j,g,rfl⟩
  · exact (hr ⟨D.parent g,(A.core.parent_eq g).symm.trans hf⟩).elim
  · have hj : A.meets j r := ⟨L.parent g,((A.std j).parent_eq g).symm.trans hf⟩
    have hji := huniq j hj
    subst j
    exact (A.std i).edge_vertex_range hx

/-- Construct every hypothesis of ContactAttachmentGeometry from the
actual source maps. In particular local_pair is now proved, not assumed. -/
def toAttachmentGeometry (h1 : D.ContactG1) (h2 : D.ContactG2)
    (hL : L.ContactLinear) : ContactAttachmentGeometry D U R where
  vertex := A.core.vertex
  wagon := A.core.wagon
  standard := A.standard
  carrier := H.contactWagonCarrier
  meets := A.meets
  standard_core := A.std_core_vertex
  meets_core := A.std_core_wagon
  core_contains := A.core.wagon_vertex_preserve
  core_contact := A.core_contact
  private_vertex_owner := fun x hx => (A.vertex_cover x).resolve_left hx
  private_vertex_meets := A.private_vertex_meets
  private_wagon := A.private_wagon
  local_pair := A.local_pair h1 h2 hL

theorem meets_of_two_vertices (h1 : D.ContactG1) (h2 : D.ContactG2)
    (h4 : ContactG4 D.contactClique 2) (hL : L.ContactLinear)
    (i : I) (r : R) (x y : U) (hxy : x ≠ y)
    (hxi : x ∈ A.standard i) (hyi : y ∈ A.standard i)
    (hxr : x ∈ H.contactWagonCarrier r) (hyr : y ∈ H.contactWagonCarrier r) :
    A.meets i r :=
  (A.toAttachmentGeometry h1 h2 hL).meets_of_two_vertices
    h1 h2 h4 i r x y hxy hxi hyi hxr hyr

include A in
theorem wagon_linearity (hD : D.ContactLinear) (h1 : D.ContactG1)
    (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique 2) (hL : L.ContactLinear) :
    ∀ r s : R, r ≠ s → (H.contactWagonCarrier r ∩ H.contactWagonCarrier s).Subsingleton :=
  (A.toAttachmentGeometry h1 h2 hL).wagon_linearity hD h1 h2 h4

end ContactPictureData
end StructuralRamsey.Girth
