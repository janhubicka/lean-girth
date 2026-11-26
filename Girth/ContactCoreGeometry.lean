import Girth.ContactLowOrder

/-! Low-order geometry of a core, in the new contact-graph language.
These are the exact local consequences used to compare wagon incidences
in different standard copies; no output-linearity premise is used. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I P)

/-- Two vertices in a common pair of distinct designated copies belong
to a unique core wagon; both copies meet it. -/
theorem contact_common_vertex_pair
    (h1 : D.ContactG1) (h2 : D.ContactG2)
    {i j : I} (hij : i ≠ j) {x y : V} (hxy : x ≠ y)
    (hxi : x ∈ D.copyCarrier i) (hyi : y ∈ D.copyCarrier i)
    (hxj : x ∈ D.copyCarrier j) (hyj : y ∈ D.copyCarrier j) :
    ∃ p, x ∈ D.contactWagonCarrier p ∧ y ∈ D.contactWagonCarrier p ∧
      D.contactMeets i p ∧ D.contactMeets j p := by
  have hn : (Sum.inl x : V ⊕ P) ≠ Sum.inl y := by
    intro he
    exact hxy (Sum.inl.inj he)
  obtain ⟨p,hx,hy⟩ := D.contact_shared_pair_in_wagon h2
    (a := Sum.inl i) (b := Sum.inl j)
    (by intro he; exact hij (Sum.inl.inj he)) hn hxi hyi hxj hyj
  have hx' : x ∈ D.contactWagonCarrier p := hx
  have hy' : y ∈ D.contactWagonCarrier p := hy
  obtain ⟨e,he,hpe,_⟩ := h1.bridge i p
    (Or.inr ⟨x,⟨hxi,hx'⟩,y,⟨hyi,hy'⟩,hxy⟩) x hxi hx'
  obtain ⟨f,hf,hpf,_⟩ := h1.bridge j p
    (Or.inr ⟨x,⟨hxj,hx'⟩,y,⟨hyj,hy'⟩,hxy⟩) x hxj hx'
  exact ⟨p,hx',hy',⟨e,he,hpe⟩,⟨f,hf,hpf⟩⟩

theorem contact_copy_pair_adjacent {i : I} {x y : V} (hxy : x ≠ y)
    (hx : x ∈ D.copyCarrier i) (hy : y ∈ D.copyCarrier i) :
    contactAdjacent D.contactClique (Sum.inl x) (Sum.inl y) := by
  exact ⟨fun he => hxy (Sum.inl.inj he),Sum.inl i,hx,hy⟩

theorem contact_copy_wagon_pair_adjacent {i : I} {p q : P} (hpq : p ≠ q)
    (hp : D.contactMeets i p) (hq : D.contactMeets i q) :
    contactAdjacent D.contactClique (Sum.inr p) (Sum.inr q) := by
  exact ⟨fun he => hpq (Sum.inr.inj he),Sum.inl i,hp,hq⟩

/-- If a copy meets two wagons, it is the only copy that meets both.
The third point of a mixed triangle is therefore forced into it. -/
theorem contact_two_wagons_force_vertex_in_copy
    (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique 2)
    {i : I} {x : V} {p q : P} (hpq : p ≠ q)
    (hip : D.contactMeets i p) (hiq : D.contactMeets i q)
    (hxp : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p))
    (hxq : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr q)) :
    x ∈ D.copyCarrier i := by
  obtain ⟨j,hx,hjp,hjq⟩ := D.contact_two_wagon_triangle_in_copy
    h4 x p q hpq hxp hxq (D.contact_copy_wagon_pair_adjacent hpq hip hiq)
  by_cases h : i = j
  · simpa only [h] using hx
  · exact (hpq (D.contact_two_common_wagons_eq h2 h hip hiq hjp hjq)).elim

/-- A weight-two alternating quadrilateral either has both real
vertices in one copy or both real vertices in both physical wagons.
The latter is impossible in a linear pretrain. -/
theorem contact_alternating_quad_in_copy
    (hlin : D.ContactLinear) (h2 : D.ContactG2)
    (h4 : ContactG4 D.contactClique 2)
    {x y : V} {p q : P} (hxy : x ≠ y) (hpq : p ≠ q)
    (hxp : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr p))
    (hxq : contactAdjacent D.contactClique (Sum.inl x) (Sum.inr q))
    (hyp : contactAdjacent D.contactClique (Sum.inl y) (Sum.inr p))
    (hyq : contactAdjacent D.contactClique (Sum.inl y) (Sum.inr q)) :
    ∃ i, x ∈ D.copyCarrier i ∧ y ∈ D.copyCarrier i := by
  rcases contact_alternating_quad_chord h4 x y p q hxy hpq hxp hxq hyp hyq
    with hVertex | hWagon
  · rcases D.contact_one_wagon_triangle h4 x y p hxp hyp hVertex
      with ⟨hxp',hyp'⟩ | ⟨i,hxi,hyi,_⟩
    · rcases D.contact_one_wagon_triangle h4 x y q hxq hyq hVertex
        with ⟨hxq',hyq'⟩ | ⟨i,hxi,hyi,_⟩
      · exact (hxy (hlin.2 p q hpq ⟨hxp',hxq'⟩ ⟨hyp',hyq'⟩)).elim
      · exact ⟨i,hxi,hyi⟩
    · exact ⟨i,hxi,hyi⟩
  · obtain ⟨i,hxi,hip,hiq⟩ := D.contact_two_wagon_triangle_in_copy
      h4 x p q hpq hxp hxq hWagon
    exact ⟨i,hxi,D.contact_two_wagons_force_vertex_in_copy h2 h4
      hpq hip hiq hyp hyq⟩

end OrderOneData
end StructuralRamsey.Girth
