import Girth.ContactCoreGeometry

/-! Section 11: two-point incidence and wagon linearity after gluing.
The interface records the elementary free-union geometry and the
LOCAL comparison of wagons in a standard copy (obtained by incidence
pullback and old linearity). It does not assume output wagon linearity.
A later adapter must construct these fields from the actual picture. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U R : Type v}

structure ContactAttachmentGeometry (D : OrderOneData V E I P) (U R : Type v) where
  vertex : V ↪ U
  wagon : P ↪ R
  standard : I → Set U
  carrier : R → Set U
  meets : I → R → Prop
  standard_core : ∀ i x, vertex x ∈ standard i ↔ x ∈ D.copyCarrier i
  meets_core : ∀ i p, meets i (wagon p) ↔ D.contactMeets i p
  core_contains : ∀ p x, x ∈ D.contactWagonCarrier p → vertex x ∈ carrier (wagon p)
  core_contact : ∀ p x, vertex x ∈ carrier (wagon p) →
    contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p)
  private_vertex_owner : ∀ x, x ∉ Set.range vertex → ∃ i, x ∈ standard i
  private_vertex_meets : ∀ i r x, x ∉ Set.range vertex →
    x ∈ standard i → x ∈ carrier r → meets i r
  private_wagon : ∀ r, r ∉ Set.range wagon →
    ∃ i, meets i r ∧ carrier r ⊆ standard i ∧ (∀ j, meets j r → j = i)
  local_pair : ∀ i r s, meets i r → meets i s →
    ∀ x y, x ≠ y → x ∈ standard i → y ∈ standard i →
      x ∈ carrier r → y ∈ carrier r →
      x ∈ carrier s → y ∈ carrier s → r = s

namespace ContactAttachmentGeometry

variable {D : OrderOneData V E I P} (A : ContactAttachmentGeometry D U R)

/-- A wagon meeting a copy and containing a point outside that copy
cannot be private. -/
theorem core_of_meets_and_outside {i : I} {r : R} {x : U}
    (hm : A.meets i r) (hx : x ∈ A.carrier r) (hxi : x ∉ A.standard i) :
    r ∈ Set.range A.wagon := by
  classical
  by_contra hr
  obtain ⟨j,_,hsub,huniq⟩ := A.private_wagon r hr
  have he := huniq i hm
  exact hxi (by rw [he]; exact hsub hx)

/-- Two distinct standards cannot share two different output wagons. -/
theorem two_shared_wagons_eq (h2 : D.ContactG2)
    {i j : I} (hij : i ≠ j) {r s : R}
    (hir : A.meets i r) (his : A.meets i s)
    (hjr : A.meets j r) (hjs : A.meets j s) : r = s := by
  classical
  have shared_core : ∀ t : R, A.meets i t → A.meets j t →
      t ∈ Set.range A.wagon := by
    intro t hit hjt
    by_contra ht
    obtain ⟨k,_,_,hk⟩ := A.private_wagon t ht
    exact hij ((hk i hit).trans (hk j hjt).symm)
  obtain ⟨p,rfl⟩ := shared_core r hir hjr
  obtain ⟨q,rfl⟩ := shared_core s his hjs
  exact congrArg A.wagon (D.contact_two_common_wagons_eq h2 hij
    ((A.meets_core i p).mp hir) ((A.meets_core i q).mp his)
    ((A.meets_core j p).mp hjr) ((A.meets_core j q).mp hjs))

/-- The two-point wagon-incidence lemma. Only local linearity and
core G1/G2/G4(2) are used; the proof does not assume the conclusion
of the subsequent global wagon-linearity proposition. -/
theorem meets_of_two_vertices (h1 : D.ContactG1) (h2 : D.ContactG2)
    (h4 : ContactG4 D.contactClique 2)
    (i : I) (r : R) (x y : U) (hxy : x ≠ y)
    (hxi : x ∈ A.standard i) (hyi : y ∈ A.standard i)
    (hxr : x ∈ A.carrier r) (hyr : y ∈ A.carrier r) : A.meets i r := by
  classical
  by_contra hn
  have hxCore : x ∈ Set.range A.vertex := by
    by_contra hx
    exact hn (A.private_vertex_meets i r x hx hxi hxr)
  have hyCore : y ∈ Set.range A.vertex := by
    by_contra hy
    exact hn (A.private_vertex_meets i r y hy hyi hyr)
  obtain ⟨u,rfl⟩ := hxCore
  obtain ⟨v,rfl⟩ := hyCore
  have huv : u ≠ v := fun he => hxy (congrArg A.vertex he)
  have hui := (A.standard_core i u).mp hxi
  have hvi := (A.standard_core i v).mp hyi
  by_cases hrCore : r ∈ Set.range A.wagon
  · obtain ⟨p,rfl⟩ := hrCore
    rcases D.contact_one_wagon_triangle h4 u v p
      (A.core_contact p u hxr) (A.core_contact p v hyr)
      (D.contact_copy_pair_adjacent huv hui hvi) with h | ⟨j,huj,hvj,hjp⟩
    · obtain ⟨e,he,hpe,_⟩ := h1.bridge i p
        (Or.inr ⟨u,⟨hui,h.1⟩,v,⟨hvi,h.2⟩,huv⟩) u hui h.1
      exact hn ((A.meets_core i p).mpr ⟨e,he,hpe⟩)
    · by_cases hij : i = j
      · subst j
        exact hn ((A.meets_core i p).mpr hjp)
      · obtain ⟨q,huq,hvq,hiq,hjq⟩ :=
          D.contact_common_vertex_pair h1 h2 hij huv hui hvi huj hvj
        have he : A.wagon p = A.wagon q :=
          A.local_pair j _ _ ((A.meets_core j p).mpr hjp) ((A.meets_core j q).mpr hjq)
            (A.vertex u) (A.vertex v) hxy ((A.standard_core j u).mpr huj)
            ((A.standard_core j v).mpr hvj) hxr hyr
            (A.core_contains q u huq) (A.core_contains q v hvq)
        exact hn (by rw [he]; exact (A.meets_core i q).mpr hiq)
  · obtain ⟨j,hjr,hsub,_⟩ := A.private_wagon r hrCore
    have hij : i ≠ j := by intro he; subst j; exact hn hjr
    have huj := (A.standard_core j u).mp (hsub hxr)
    have hvj := (A.standard_core j v).mp (hsub hyr)
    obtain ⟨q,huq,hvq,_,hjq⟩ :=
      D.contact_common_vertex_pair h1 h2 hij huv hui hvi huj hvj
    have he : r = A.wagon q :=
      A.local_pair j r _ hjr ((A.meets_core j q).mpr hjq)
        (A.vertex u) (A.vertex v) hxy (hsub hxr) (hsub hyr)
        hxr hyr (A.core_contains q u huq) (A.core_contains q v hvq)
    exact hrCore ⟨q,he.symm⟩

/-- First part of the global-linearity argument: when a shared point is
private, two distinct output wagons cannot share a second point. -/
theorem wagon_pair_with_private (h1 : D.ContactG1) (h2 : D.ContactG2)
    (h4 : ContactG4 D.contactClique 2)
    {r s : R} {x y : U} (hxy : x ≠ y)
    (hxr : x ∈ A.carrier r) (hyr : y ∈ A.carrier r)
    (hxs : x ∈ A.carrier s) (hys : y ∈ A.carrier s)
    (hyPrivate : y ∉ Set.range A.vertex) : r = s := by
  classical
  by_contra hne
  have noStd : ∀ i, x ∈ A.standard i → y ∈ A.standard i → False := by
    intro i hxi hyi
    apply hne
    exact A.local_pair i r s
      (A.meets_of_two_vertices h1 h2 h4 i r x y hxy hxi hyi hxr hyr)
      (A.meets_of_two_vertices h1 h2 h4 i s x y hxy hxi hyi hxs hys)
      x y hxy hxi hyi hxr hyr hxs hys
  obtain ⟨i,hyi⟩ := A.private_vertex_owner y hyPrivate
  have hir := A.private_vertex_meets i r y hyPrivate hyi hyr
  have his := A.private_vertex_meets i s y hyPrivate hyi hys
  have hxi : x ∉ A.standard i := fun h => noStd i h hyi
  by_cases hxCore : x ∈ Set.range A.vertex
  · obtain ⟨u,rfl⟩ := hxCore
    obtain ⟨p,rfl⟩ := A.core_of_meets_and_outside hir hxr hxi
    obtain ⟨q,rfl⟩ := A.core_of_meets_and_outside his hxs hxi
    have hpq : p ≠ q := fun he => hne (congrArg A.wagon he)
    have hui := D.contact_two_wagons_force_vertex_in_copy h2 h4 hpq
      ((A.meets_core i p).mp hir) ((A.meets_core i q).mp his)
      (A.core_contact p u hxr) (A.core_contact q u hxs)
    exact hxi ((A.standard_core i u).mpr hui)
  · obtain ⟨j,hxj⟩ := A.private_vertex_owner x hxCore
    have hij : i ≠ j := by intro he; subst j; exact hxi hxj
    exact hne (A.two_shared_wagons_eq h2 hij hir his
      (A.private_vertex_meets j r x hxCore hxj hxr)
      (A.private_vertex_meets j s x hxCore hxj hxs))

/-- Global wagon linearity, from the actual low-order contact conditions
and the free-union/local-linearity interface above. -/
theorem wagon_linearity (hlin : D.ContactLinear)
    (h1 : D.ContactG1) (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique 2) :
    ∀ r s : R, r ≠ s → (A.carrier r ∩ A.carrier s).Subsingleton := by
  classical
  intro r s hne x hx y hy
  by_contra hxy
  have noStd : ∀ i, x ∈ A.standard i → y ∈ A.standard i → False := by
    intro i hxi hyi
    apply hne
    exact A.local_pair i r s
      (A.meets_of_two_vertices h1 h2 h4 i r x y hxy hxi hyi hx.1 hy.1)
      (A.meets_of_two_vertices h1 h2 h4 i s x y hxy hxi hyi hx.2 hy.2)
      x y hxy hxi hyi hx.1 hy.1 hx.2 hy.2
  by_cases hyCore : y ∈ Set.range A.vertex
  · by_cases hxCore : x ∈ Set.range A.vertex
    · obtain ⟨u,rfl⟩ := hxCore
      obtain ⟨v,rfl⟩ := hyCore
      have core_of_pair : ∀ t : R, A.vertex u ∈ A.carrier t →
          A.vertex v ∈ A.carrier t → t ∈ Set.range A.wagon := by
        intro t hu hv
        by_contra ht
        obtain ⟨i,_,hsub,_⟩ := A.private_wagon t ht
        exact noStd i (hsub hu) (hsub hv)
      obtain ⟨p,rfl⟩ := core_of_pair r hx.1 hy.1
      obtain ⟨q,rfl⟩ := core_of_pair s hx.2 hy.2
      have huv : u ≠ v := fun he => hxy (congrArg A.vertex he)
      have hpq : p ≠ q := fun he => hne (congrArg A.wagon he)
      obtain ⟨i,hui,hvi⟩ := D.contact_alternating_quad_in_copy
        hlin h2 h4 huv hpq
        (A.core_contact p u hx.1) (A.core_contact q u hx.2)
        (A.core_contact p v hy.1) (A.core_contact q v hy.2)
      exact noStd i ((A.standard_core i u).mpr hui) ((A.standard_core i v).mpr hvi)
    · exact hne (A.wagon_pair_with_private h1 h2 h4 (fun he => hxy he.symm)
        hy.1 hx.1 hy.2 hx.2 hxCore)
  · exact hne (A.wagon_pair_with_private h1 h2 h4 hxy
      hx.1 hy.1 hx.2 hy.2 hyCore)

end ContactAttachmentGeometry
end StructuralRamsey.Girth
