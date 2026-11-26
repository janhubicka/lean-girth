import Girth.ContactExpansionSlots
import Girth.ContactExpandedPolygon

/-! Construct the expanded polygon, including its exact weight.
The only vertices in the enumeration are the original points and the
selected fresh wagons. Summing outgoing weights over the even slots
and the retained odd slots gives the original total, since the
weight-two real-real side becomes two weight-one mixed sides. -/

namespace StructuralRamsey.Girth

universe v
variable {V E I P U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData.SidePlan
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    {B : ContactPolygon U R} (S : A.SidePlan B)

private def halfIndex (k : Fin (2*B.length)) : Fin B.length :=
  ⟨k.val / 2,by have := k.isLt; omega⟩

private theorem halfIndex_even (i : Fin B.length) :
    halfIndex (contactEvenSlot i) = i := by
  apply Fin.ext
  change 2*i.val / 2 = i.val
  omega

private theorem halfIndex_odd (i : Fin B.length) :
    halfIndex (contactOddSlot i) = i := by
  apply Fin.ext
  change (2*i.val+1) / 2 = i.val
  omega

/-- A value on the ambient doubled positions. The default for an
unselected odd slot is immaterial because that slot is never enumerated. -/
private def slotValue (k : Fin (2*B.length)) : U ⊕ R :=
  if k.val % 2 = 0 then B.vertex (halfIndex k)
  else match S.insert (halfIndex k) with
    | none => B.vertex (halfIndex k)
    | some p => Sum.inr (A.core.wagon p)

private theorem slotValue_even (i : Fin B.length) :
    S.slotValue (contactEvenSlot i) = B.vertex i := by
  have h : (contactEvenSlot i).val % 2 = 0 := by
    change (2*i.val) % 2 = 0
    omega
  simp only [slotValue,h,if_true,halfIndex_even]

private theorem slotValue_odd (i : Fin B.length) (p : P)
    (hi : S.insert i = some p) :
    S.slotValue (contactOddSlot i) = Sum.inr (A.core.wagon p) := by
  have h : (contactOddSlot i).val % 2 ≠ 0 := by
    change (2*i.val+1) % 2 ≠ 0
    omega
  simp only [slotValue,if_neg h,halfIndex_odd,hi]

private noncomputable def expandedVertex (k : Fin (ContactSlots.kept S.insert).card) :
    U ⊕ R :=
  S.slotValue (ContactSlots.enum S.insert k)

private theorem expanded_original (i : Fin B.length) :
    S.expandedVertex (ContactSlots.original S.insert i) = B.vertex i := by
  unfold expandedVertex
  rw [ContactSlots.original_slot,S.slotValue_even]

private theorem expanded_inserted (i : Fin B.length) (p : P)
    (h : S.insert i = some p) :
    S.expandedVertex (ContactSlots.inserted S.insert i (by simp [h])) =
      Sum.inr (A.core.wagon p) := by
  unfold expandedVertex
  rw [ContactSlots.inserted_slot,S.slotValue_odd i p h]

private theorem expanded_injective (hb : B.Bad H.contactClique) :
    Function.Injective S.expandedVertex := by
  classical
  intro k l he
  rcases ContactSlots.cover S.insert k with ⟨i,rfl⟩ | ⟨i,hi,rfl⟩
  · rcases ContactSlots.cover S.insert l with ⟨j,rfl⟩ | ⟨j,hj,rfl⟩
    · rw [S.expanded_original,S.expanded_original] at he
      exact congrArg (ContactSlots.original S.insert) (B.vertex_injective he)
    · cases h : S.insert j with
      | none => exact (hj h).elim
      | some p =>
        rw [S.expanded_original,S.expanded_inserted j p h] at he
        exact (S.split_fresh hb j p h i he).elim
  · cases h : S.insert i with
    | none => exact (hi h).elim
    | some p =>
      rcases ContactSlots.cover S.insert l with ⟨j,rfl⟩ | ⟨j,hj,rfl⟩
      · rw [S.expanded_inserted i p h,S.expanded_original] at he
        exact (S.split_fresh hb i p h j he.symm).elim
      · cases h' : S.insert j with
        | none => exact (hj h').elim
        | some p' =>
          rw [S.expanded_inserted i p h,S.expanded_inserted j p' h'] at he
          have hp : p = p' := A.core.wagon.injective (Sum.inr.inj he)
          subst p'
          have hij := S.split_injective hb i j p h h'
          subst j
          rfl

private noncomputable def expandedPolygon (hb : B.Bad H.contactClique) : ContactPolygon U R where
  length := (ContactSlots.kept S.insert).card
  hlength := B.hlength.trans (ContactSlots.count_ge S.insert)
  vertex := S.expandedVertex
  vertex_injective := S.expanded_injective hb

/-- The sum of outgoing weights over the retained positions, split
into original and inserted positions. The index proof is independent
of all graph and wagon hypotheses. -/
private theorem sum_expanded_slots
    (wt : Fin (ContactSlots.kept S.insert).card → ℕ) :
    (∑ k, wt k) =
      (∑ i : Fin B.length, wt (ContactSlots.original S.insert i)) +
        ∑ i : Fin B.length,
          if h : S.insert i ≠ none then wt (ContactSlots.inserted S.insert i h) else 0 := by
  classical
  let o := ContactSlots.original S.insert
  let d : Fin B.length → Fin (ContactSlots.kept S.insert).card := fun i =>
    if h : S.insert i ≠ none then ContactSlots.inserted S.insert i h else o i
  let orig : Finset (Fin (ContactSlots.kept S.insert).card) := Finset.univ.image o
  let add : Finset (Fin (ContactSlots.kept S.insert).card) :=
    (ContactSlots.selected S.insert).image d
  have hd : Disjoint orig add := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hk
    obtain ⟨j,hj,hj'⟩ := Finset.mem_image.mp hk'
    have hn := (ContactSlots.mem_selected S.insert j).mp hj
    have he : o i = ContactSlots.inserted S.insert j hn := by
      calc
        o i = k := hi
        _ = d j := hj'.symm
        _ = ContactSlots.inserted S.insert j hn := by simp only [d,dif_pos hn]
    exact ContactSlots.original_ne_inserted S.insert i j hn he
  have hu : orig ∪ add = Finset.univ := by
    ext k
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      rcases ContactSlots.cover S.insert k with ⟨i,hi⟩ | ⟨i,hn,hi⟩
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨i,Finset.mem_univ _,hi⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i,(ContactSlots.mem_selected S.insert i).mpr hn,
            by simpa only [d,dif_pos hn] using hi⟩))
  have ho : (∑ k ∈ orig, wt k) = ∑ i : Fin B.length, wt (o i) := by
    unfold orig
    rw [Finset.sum_image]
    intro i _ j _ he
    exact ContactSlots.original_injective S.insert he
  have ha : (∑ k ∈ add, wt k) =
      ∑ i ∈ ContactSlots.selected S.insert, wt (d i) := by
    unfold add
    rw [Finset.sum_image]
    intro i hi j hj he
    have hi' := (ContactSlots.mem_selected S.insert i).mp hi
    have hj' := (ContactSlots.mem_selected S.insert j).mp hj
    have hh : ContactSlots.inserted S.insert i hi' =
        ContactSlots.inserted S.insert j hj' := by
      simpa only [d,dif_pos hi',dif_pos hj'] using he
    exact ContactSlots.inserted_injective S.insert hi' hj' hh
  have hf : (∑ i ∈ ContactSlots.selected S.insert, wt (d i)) =
      ∑ i : Fin B.length,
        if h : S.insert i ≠ none then wt (ContactSlots.inserted S.insert i h) else 0 := by
    unfold ContactSlots.selected
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : S.insert i ≠ none <;> simp [d,h]
  calc
    (∑ k, wt k) = ∑ k ∈ orig ∪ add, wt k := by rw [hu]
    _ = (∑ k ∈ orig, wt k) + ∑ k ∈ add, wt k := Finset.sum_union hd
    _ = _ := by rw [ho,ha,hf]

/-- Subdivision preserves doubled weight exactly. -/
theorem expanded_weight (hb : B.Bad H.contactClique) :
    (S.expandedPolygon hb).twiceWeight = B.twiceWeight := by
  classical
  let wt : Fin (ContactSlots.kept S.insert).card → ℕ :=
    fun k => contactWeight (S.expandedVertex k) (S.expandedVertex (cyclicSucc k))
  change (∑ k, wt k) = B.twiceWeight
  rw [S.sum_expanded_slots wt,← Finset.sum_add_distrib]
  unfold ContactPolygon.twiceWeight
  apply Finset.sum_congr rfl
  intro i _
  cases h : S.insert i with
  | none =>
    have hn : ¬ S.insert i ≠ none := fun he => he h
    rw [dif_neg hn,Nat.add_zero]
    change contactWeight (S.expandedVertex (ContactSlots.original S.insert i))
      (S.expandedVertex (cyclicSucc (ContactSlots.original S.insert i))) = _
    rw [ContactSlots.direct_next S.insert i h,S.expanded_original,S.expanded_original]
  | some p =>
    have hn : S.insert i ≠ none := by simp [h]
    rw [dif_pos hn]
    change contactWeight (S.expandedVertex (ContactSlots.original S.insert i))
      (S.expandedVertex (cyclicSucc (ContactSlots.original S.insert i))) +
      contactWeight (S.expandedVertex (ContactSlots.inserted S.insert i hn))
        (S.expandedVertex (cyclicSucc (ContactSlots.inserted S.insert i hn))) = _
    rw [ContactSlots.split_first S.insert i hn,ContactSlots.split_second S.insert i hn,
      S.expanded_original,S.expanded_original,S.expanded_inserted i p h]
    obtain ⟨x,y,hx,hy,_,_⟩ := S.split i p h
    rw [hx,hy]
    exact (contactWeight_subdivide x y (A.core.wagon p)).symm

/-- The finite expansion exists for every actual geometric subdivision
plan of a bad polygon. All fields, including the weight, are proved. -/
noncomputable def expand (hb : B.Bad H.contactClique) : S.Expansion where
  polygon := S.expandedPolygon hb
  original := ContactSlots.original S.insert
  inserted := fun i p h => ContactSlots.inserted S.insert i (by simp [h])
  original_eq := S.expanded_original
  inserted_eq := S.expanded_inserted
  cover := by
    intro k
    rcases ContactSlots.cover S.insert k with ⟨i,hi⟩ | ⟨i,hi,he⟩
    · exact Or.inl ⟨i,hi⟩
    · cases h : S.insert i with
      | none => exact (hi h).elim
      | some p => exact Or.inr ⟨i,p,h,he⟩
  direct_next := ContactSlots.direct_next S.insert
  split_first := fun i p h => ContactSlots.split_first S.insert i (by simp [h])
  split_second := fun i p h => ContactSlots.split_second S.insert i (by simp [h])
  weight_eq := S.expanded_weight hb

end ContactPictureData.SidePlan

namespace ContactPictureCopies
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)

/-- Positive-core G4 preservation: neither a boundary decomposition
nor subdivision existence is an assumption. -/
theorem preserves_g4_positive {q : ℕ}
    (hlin : D.ContactLinear) (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (hcore : ContactG4 D.contactClique q) (hlocal : ContactG4 L.contactClique q) :
    ContactG4 H.contactClique q := by
  apply contactG4_of_no_bad
  intro B hw hb
  let S := C.sidePlan B hb.1
  exact (S.expand hb).false_of_core_G4 C hlin h1 h2 htwo hcore hlocal hw hb

end ContactPictureCopies
end StructuralRamsey.Girth
