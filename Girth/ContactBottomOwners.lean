import Girth.ContactBottomBoundary

/-! The special bottom side assignment.
The active strip is absorbed by each lifted copy that contains one
of its edges. Thus a mixed side with both endpoints in the core is
a physical vertex--edge incidence. At its wagon endpoint the other
side cannot also be such an incidence (badness). Assign the physical
side to the constituent of that other side. This eliminates single
mixed-side segments without changing the polygon or its weight. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

/-- The one-edge trace of a lifted transversal copy on the active
strip, whenever it contains an edge of that strip. This is the
projection/absorption lemma of the manuscript. -/
def BottomAbsorption : Prop :=
  ∀ c : I × I₀, ∀ e : E, A.core.edge e ∈ H.copyEdges c →
    ∀ x : V, A.core.vertex x ∈ H.copyCarrier c → x ∈ D.edgeCarrier e

include A in
theorem bottom_wagon_eq_edge (hinj : Function.Injective H.parent)
    (e : F) :
    H.contactWagonCarrier (H.parent e) = H.edgeCarrier e := by
  ext x
  constructor
  · rintro ⟨f,hf,hx⟩
    have he := hinj hf
    simpa only [he] using hx
  · intro hx
    exact ⟨e,rfl,hx⟩

theorem core_wagon_eq_core_edge (h0 : ∀ e, D.parent e = e)
    (hinj : Function.Injective H.parent) (p : E) :
    H.contactWagonCarrier (A.core.wagon p) = H.edgeCarrier (A.core.edge p) := by
  have he : H.parent (A.core.edge p) = A.core.wagon p := by rw [A.core.parent_eq,h0]
  rw [← he]
  exact A.bottom_wagon_eq_edge hinj _

/-- If a constituent contains a core wagon label at the bottom
cut, it contains the entire carrier of that wagon. -/
theorem bottom_constituent_contains_wagon (h0 : ∀ e, D.parent e = e)
    (hinj : Function.Injective H.parent)
    (a : I ⊕ E) (p : E)
    (hp : Sum.inr (A.core.wagon p) ∈ A.constituent a) :
    H.contactWagonClique (A.core.wagon p) ⊆ A.constituent a := by
  have hp' : Sum.inr p ∈ A.coreConstituent a :=
    (A.core_constituent_iff a (Sum.inr p)).mp hp
  intro z hz
  cases z with
  | inr r =>
    have hr : r = A.core.wagon p := hz
    simpa only [hr] using hp
  | inl x =>
    change x ∈ H.contactWagonCarrier (A.core.wagon p) at hz
    rw [A.core_wagon_eq_core_edge h0 hinj p] at hz
    obtain ⟨u,rfl⟩ := A.core.edge_vertex_range hz
    apply (A.core_constituent_iff a (Sum.inl u)).mpr
    have hu := A.core.edge_vertex_reflect p u hz
    cases a with
    | inr e =>
      have he : p = D.parent e := hp'
      rw [h0] at he
      subst e
      exact hu
    | inl i =>
      have hm : D.contactMeets i p := hp'
      obtain ⟨e,he,hpe⟩ := hm
      have hep : e = p := (h0 e).symm.trans hpe
      subst e
      obtain ⟨f,hf⟩ := (A.std_core_edge i p).mpr he
      apply (A.std_core_vertex i u).mp
      have hx : A.core.vertex u ∈ H.edgeCarrier ((A.std i).edge f) := by
        rw [hf]
        exact hz
      exact (A.std i).edge_vertex_range hx

end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

/-- At the bottom cut every actual side already has a constituent.
There is no subdivision in this case. -/
theorem bottom_side_constituent (hinj : Function.Injective H.parent)
    {z t : U ⊕ R} (h : contactAdjacent H.contactClique z t) :
    ∃ a : I ⊕ E, z ∈ A.constituent a ∧ t ∈ A.constituent a := by
  obtain ⟨_,b,hz,ht⟩ := h
  cases b with
  | inl b =>
    exact ⟨Sum.inl b.1,C.copy_clique_in_domain b.1 b.2 hz,
      C.copy_clique_in_domain b.1 b.2 ht⟩
  | inr r =>
    obtain ⟨e,he⟩ := A.parent_surjective r
    subst r
    obtain ⟨a,ha,hp⟩ := A.edge_contact_constituent e
    have hsub : H.contactWagonClique (H.parent e) ⊆ A.constituent a := by
      intro x hx
      cases x with
      | inl u =>
        apply ha u
        rw [← A.bottom_wagon_eq_edge hinj]
        exact hx
      | inr p =>
        have hp' : p = H.parent e := hx
        simpa only [hp'] using hp
    exact ⟨a,hsub hz,hsub ht⟩

/-- Both endpoints of a mixed core side lie in the actual bottom
wagon clique, by absorption of the active strip in a lifted copy. -/
theorem bottom_mixed_core_incidence (h0 : ∀ e, D.parent e = e)
    (hinj : Function.Injective H.parent) (habs : A.BottomAbsorption)
    (x : V) (p : E)
    (h : contactAdjacent H.contactClique (Sum.inl (A.core.vertex x))
      (Sum.inr (A.core.wagon p))) :
    A.core.vertex x ∈ H.contactWagonCarrier (A.core.wagon p) := by
  obtain ⟨_,b,hx,hp⟩ := h
  cases b with
  | inr r =>
    have he : A.core.wagon p = r := hp
    change A.core.vertex x ∈ H.contactWagonCarrier r at hx
    simpa only [← he] using hx
  | inl b =>
    obtain ⟨e,he,hpe⟩ := hp
    have hp' : H.parent (A.core.edge p) = A.core.wagon p := by
      rw [A.core.parent_eq,h0]
    have heq : e = A.core.edge p := hinj (hpe.trans hp'.symm)
    subst e
    have hx' := habs b p he x hx
    exact A.core.wagon_vertex_preserve p x ⟨p,h0 p,hx'⟩

end ContactPictureCopies

/-- A chosen cyclic predecessor, inverse to cyclic successor. -/
noncomputable def contactPrev {n : ℕ} (i : Fin n) : Fin n :=
  Classical.choose (contactSucc_surjective i)

theorem contactSucc_prev {n : ℕ} (i : Fin n) : cyclicSucc (contactPrev i) = i :=
  Classical.choose_spec (contactSucc_surjective i)

theorem contactPrev_succ {n : ℕ} (i : Fin n) : contactPrev (cyclicSucc i) = i :=
  ContactCyclicRestriction.contactCyclicSucc_injective (contactSucc_prev (cyclicSucc i))

namespace ContactPictureData
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

def BottomForward (B : ContactPolygon U R) (k : Fin B.length) : Prop :=
  ∃ x : V, ∃ p : E,
    B.vertex k = Sum.inl (A.core.vertex x) ∧
    B.vertex (cyclicSucc k) = Sum.inr (A.core.wagon p)

def BottomBackward (B : ContactPolygon U R) (k : Fin B.length) : Prop :=
  ∃ x : V, ∃ p : E,
    B.vertex k = Sum.inr (A.core.wagon p) ∧
    B.vertex (cyclicSucc k) = Sum.inl (A.core.vertex x)

end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I E} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

theorem forward_next_unprotected
    (h0 : ∀ e, D.parent e = e) (hinj : Function.Injective H.parent)
    (habs : A.BottomAbsorption) (B : ContactPolygon U R)
    (hb : B.Bad H.contactClique) (k : Fin B.length)
    (hk : A.BottomForward B k) :
    ¬ A.BottomForward B (cyclicSucc k) ∧
      ¬ A.BottomBackward B (cyclicSucc k) := by
  obtain ⟨x,p,hx,hp⟩ := hk
  constructor
  · rintro ⟨y,r,hy,hr⟩
    rw [hp] at hy
    cases hy
  · rintro ⟨y,r,hr,hy⟩
    have he : r = p := A.core.wagon.injective (Sum.inr.inj (hr.symm.trans hp))
    subst r
    have h1 := hb.1 k
    rw [hx,hp] at h1
    have h2 := contactAdjacent_symm (hb.1 (cyclicSucc k))
    rw [hp,hy] at h2
    apply B.bad_no_three_successive hb (Sum.inr (A.core.wagon p)) k
    · rw [hx]
      exact C.bottom_mixed_core_incidence h0 hinj habs x p h1
    · rw [hp]
      rfl
    · rw [hy]
      exact C.bottom_mixed_core_incidence h0 hinj habs y p h2

theorem backward_prev_unprotected
    (h0 : ∀ e, D.parent e = e) (hinj : Function.Injective H.parent)
    (habs : A.BottomAbsorption) (B : ContactPolygon U R)
    (hb : B.Bad H.contactClique) (k : Fin B.length)
    (hk : A.BottomBackward B k) :
    ¬ A.BottomForward B (contactPrev k) ∧
      ¬ A.BottomBackward B (contactPrev k) := by
  obtain ⟨x,p,hp,hx⟩ := hk
  constructor
  · intro hf
    have h := (C.forward_next_unprotected h0 hinj habs B hb (contactPrev k) hf).2
    rw [contactSucc_prev] at h
    exact h ⟨x,p,hp,hx⟩
  · rintro ⟨y,r,hr,hy⟩
    rw [contactSucc_prev,hp] at hy
    cases hy

/-- An outgoing-side owner assignment with the required merging
at the wagon end of each mixed core side. -/
theorem bottom_owner_assignment
    (h0 : ∀ e, D.parent e = e) (hinj : Function.Injective H.parent)
    (habs : A.BottomAbsorption) (B : ContactPolygon U R)
    (hb : B.Bad H.contactClique) :
    ∃ owner : Fin B.length → I ⊕ E,
      (∀ k, B.vertex k ∈ A.constituent (owner k) ∧
        B.vertex (cyclicSucc k) ∈ A.constituent (owner k)) ∧
      (∀ k, A.BottomForward B k → owner k = owner (cyclicSucc k)) ∧
      (∀ k, A.BottomBackward B k → owner k = owner (contactPrev k)) := by
  classical
  have hex : ∀ k, ∃ a : I ⊕ E,
      B.vertex k ∈ A.constituent a ∧ B.vertex (cyclicSucc k) ∈ A.constituent a :=
    fun k => C.bottom_side_constituent hinj (hb.1 k)
  choose out hout using hex
  let owner : Fin B.length → I ⊕ E := fun k =>
    if A.BottomForward B k then out (cyclicSucc k)
    else if A.BottomBackward B k then out (contactPrev k) else out k
  have hunprotected : ∀ k, ¬ A.BottomForward B k → ¬ A.BottomBackward B k →
      owner k = out k := by
    intro k hf hb'
    simp [owner,hf,hb']
  refine ⟨owner,?_,?_,?_⟩
  · intro k
    by_cases hf : A.BottomForward B k
    · obtain ⟨x,p,hx,hp⟩ := hf
      have hm := (hout (cyclicSucc k)).1
      rw [hp] at hm
      have hs := hb.1 k
      rw [hx,hp] at hs
      have hinc := C.bottom_mixed_core_incidence h0 hinj habs x p hs
      have hleft := A.bottom_constituent_contains_wagon h0 hinj
        (out (cyclicSucc k)) p hm (show Sum.inl (A.core.vertex x) ∈ H.contactWagonClique (A.core.wagon p) from hinc)
      simpa only [owner,if_pos (show A.BottomForward B k from ⟨x,p,hx,hp⟩),hx,hp] using
        And.intro hleft hm
    · by_cases hb' : A.BottomBackward B k
      · obtain ⟨x,p,hp,hx⟩ := hb'
        have hm := (hout (contactPrev k)).2
        rw [contactSucc_prev,hp] at hm
        have hs := contactAdjacent_symm (hb.1 k)
        rw [hp,hx] at hs
        have hinc := C.bottom_mixed_core_incidence h0 hinj habs x p hs
        have hright := A.bottom_constituent_contains_wagon h0 hinj
          (out (contactPrev k)) p hm (show Sum.inl (A.core.vertex x) ∈ H.contactWagonClique (A.core.wagon p) from hinc)
        simpa only [owner,if_neg hf,if_pos (show A.BottomBackward B k from ⟨x,p,hp,hx⟩),hp,hx] using
          And.intro hm hright
      · rw [hunprotected k hf hb']
        exact hout k
  · intro k hf
    have hnext := C.forward_next_unprotected h0 hinj habs B hb k hf
    rw [hunprotected _ hnext.1 hnext.2]
    simp [owner,hf]
  · intro k hb'
    have hprev := C.backward_prev_unprotected h0 hinj habs B hb k hb'
    have hf : ¬ A.BottomForward B k := by
      rintro ⟨y,r,hy,hr⟩
      obtain ⟨x,p,hp,hx⟩ := hb'
      rw [hp] at hy
      cases hy
    rw [hunprotected _ hprev.1 hprev.2]
    simp [owner,hf,hb']

end ContactPictureCopies
end StructuralRamsey.Girth
