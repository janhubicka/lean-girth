import Girth.ContactBoundary

/-! Existence and geometry of the side subdivisions.
A side not in any constituent must be a real-real side in a core wagon.
The two half-sides have constituent witnesses.  Badness gives fresh,
pairwise distinct inserted wagon labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F R V₀ E₀ I₀ P₀ : Type v}

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

theorem edge_contact_constituent (e : F) :
    ∃ a : I ⊕ E,
      (∀ x ∈ H.edgeCarrier e, Sum.inl x ∈ A.constituent a) ∧
      Sum.inr (H.parent e) ∈ A.constituent a := by
  rcases A.edge_cover e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
  · refine ⟨Sum.inr f,?_,?_⟩
    · intro x hx
      obtain ⟨y,rfl⟩ := A.core.edge_vertex_range hx
      exact ⟨Sum.inl y,A.core.edge_vertex_reflect f y hx,rfl⟩
    · rw [A.core.parent_eq]
      exact ⟨Sum.inr (D.parent f),rfl,rfl⟩
  · refine ⟨Sum.inl i,?_,?_⟩
    · intro x hx
      exact ((A.std i).real_in_range_contactMap x).mpr ((A.std i).edge_vertex_range hx)
    · rw [(A.std i).parent_eq]
      exact ⟨Sum.inr (L.parent f),rfl⟩

theorem mixed_incidence_constituent (r : R) (x : U)
    (hx : x ∈ H.contactWagonCarrier r) :
    ∃ a : I ⊕ E, Sum.inl x ∈ A.constituent a ∧ Sum.inr r ∈ A.constituent a := by
  obtain ⟨e,he,hxe⟩ := hx
  obtain ⟨a,ha,hp⟩ := A.edge_contact_constituent e
  exact ⟨a,ha x hxe,by simpa only [he] using hp⟩

/-- An unshared wagon is wholly contained in its one standard. -/
theorem private_wagon_clique_constituent (r : R)
    (hpriv : r ∉ Set.range A.core.wagon) :
    ∃ a : I ⊕ E, H.contactWagonClique r ⊆ A.constituent a := by
  obtain ⟨i,hm,hsub,_⟩ := A.private_wagon r hpriv
  refine ⟨Sum.inl i,?_⟩
  intro z hz
  cases z with
  | inl x => exact ((A.std i).real_in_range_contactMap x).mpr (hsub hz)
  | inr p =>
    have hp : p = r := hz
    subst p
    exact ((A.std i).wagon_in_range_contactMap r).mpr hm

end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)
include C

/-- If an actual contact side has no constituent, it is necessarily
a real-real side in a core wagon, and both half-sides have constituent
witnesses. The choice of two different half-side constituents is
automatic from the absence of a common constituent. -/
theorem side_or_subdivide {z t : U ⊕ R}
    (h : contactAdjacent H.contactClique z t) :
    (∃ a : I ⊕ E, z ∈ A.constituent a ∧ t ∈ A.constituent a) ∨
    ∃ (x y : U) (p : P), z = Sum.inl x ∧ t = Sum.inl y ∧
      x ∈ H.contactWagonCarrier (A.core.wagon p) ∧
      y ∈ H.contactWagonCarrier (A.core.wagon p) := by
  classical
  obtain ⟨hne,b,hz,ht⟩ := h
  cases b with
  | inl b =>
    exact Or.inl ⟨Sum.inl b.1,C.copy_clique_in_domain b.1 b.2 hz,
      C.copy_clique_in_domain b.1 b.2 ht⟩
  | inr r =>
    cases z with
    | inr p =>
      have hp : p = r := hz
      subst p
      cases t with
      | inr s =>
        exact (hne (congrArg Sum.inr (show s = r from ht).symm)).elim
      | inl y =>
        obtain ⟨a,ha,hb⟩ := A.mixed_incidence_constituent r y ht
        exact Or.inl ⟨a,hb,ha⟩
    | inl x =>
      cases t with
      | inr p =>
        have hp : p = r := ht
        subst p
        exact Or.inl (A.mixed_incidence_constituent r x hz)
      | inl y =>
        by_cases hcore : r ∈ Set.range A.core.wagon
        · obtain ⟨p,rfl⟩ := hcore
          exact Or.inr ⟨x,y,p,rfl,rfl,hz,ht⟩
        · obtain ⟨a,ha⟩ := A.private_wagon_clique_constituent r hcore
          exact Or.inl ⟨a,ha hz,ha ht⟩

/-- A bad polygon cannot be contained in a standard contact domain,
since the reflected local polygon has the same weights, and local G4
would give a covered triangle or chord. -/
theorem bad_not_in_standard {q : ℕ} (h1 : D.ContactG1) (h2 : D.ContactG2)
    (htwo : ∀ i r x y, x ≠ y → x ∈ A.standard i → y ∈ A.standard i →
      x ∈ H.contactWagonCarrier r → y ∈ H.contactWagonCarrier r → A.meets i r)
    (h4 : ContactG4 L.contactClique q)
    (B : ContactPolygon U R) (hw : B.twiceWeight ≤ 2*q)
    (hb : B.Bad H.contactClique) (i : I) :
    ¬ ∀ k, B.vertex k ∈ A.contactDomain i := by
  classical
  intro hall
  choose vtx hvtx using hall
  let P₁ : ContactPolygon V₀ P₀ := {
    length := B.length
    hlength := B.hlength
    vertex := vtx
    vertex_injective := by
      intro a b he
      apply B.vertex_injective
      exact (hvtx a).symm.trans
        ((congrArg (A.std i).contactMap he).trans (hvtx b))
  }
  have hc : P₁.IsCycle L.contactClique := by
    intro k
    apply C.reflect_adjacency h1 h2 htwo i
    change contactAdjacent H.contactClique ((A.std i).contactMap (vtx k))
      ((A.std i).contactMap (vtx (cyclicSucc k)))
    rw [hvtx,hvtx]
    exact hb.1 k
  have hweight : P₁.twiceWeight = B.twiceWeight := by
    unfold ContactPolygon.twiceWeight
    apply Finset.sum_congr rfl
    intro k _
    change contactWeight (vtx k) (vtx (cyclicSucc k)) =
      contactWeight (B.vertex k) (B.vertex (cyclicSucc k))
    rw [← hvtx k,← hvtx (cyclicSucc k)]
    cases vtx k <;> cases vtx (cyclicSucc k) <;> rfl
  rcases contactSharedChordBound_of_G4 h4 P₁ hc (by rw [hweight]; exact hw)
    with hcover | hchord
  · obtain ⟨a,ha⟩ := hcover
    apply hb.2.1
    cases a with
    | inl a =>
      refine ⟨Sum.inl (i,a),?_⟩
      intro k
      rw [← hvtx k]
      exact (C.copy_clique_iff i a (vtx k)).mpr (ha k)
    | inr p =>
      refine ⟨Sum.inr ((A.std i).wagon p),?_⟩
      intro k
      rw [← hvtx k]
      exact (A.std i).wagon_clique_preserve p (ha k)
  · obtain ⟨a,b,hnc,hc⟩ := P₁.shared_hasChord hchord
    apply hb.2.2
    refine ⟨a,b,hnc,?_⟩
    rw [← hvtx a,← hvtx b]
    exact C.preserve_adjacency i hc

end ContactPictureCopies

namespace ContactPictureData
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} (A : ContactPictureData D L H)

/-- Choice of which original sides are subdivided. A split is allowed
exactly when no constituent contains its original pair. -/
structure SidePlan (B : ContactPolygon U R) where
  insert : Fin B.length → Option P
  direct : ∀ i, insert i = none →
    ∃ a : I ⊕ E, B.vertex i ∈ A.constituent a ∧
      B.vertex (cyclicSucc i) ∈ A.constituent a
  split : ∀ i p, insert i = some p →
    ∃ x y : U, B.vertex i = Sum.inl x ∧ B.vertex (cyclicSucc i) = Sum.inl y ∧
      x ∈ H.contactWagonCarrier (A.core.wagon p) ∧
      y ∈ H.contactWagonCarrier (A.core.wagon p)
  not_direct : ∀ i p, insert i = some p →
    ¬ ∃ a : I ⊕ E, B.vertex i ∈ A.constituent a ∧
      B.vertex (cyclicSucc i) ∈ A.constituent a

namespace SidePlan
variable {A : ContactPictureData D L H} {B : ContactPolygon U R}
    (S : A.SidePlan B)

theorem split_endpoints (i : Fin B.length) (p : P) (hi : S.insert i = some p) :
    B.vertex i ∈ H.contactWagonClique (A.core.wagon p) ∧
      B.vertex (cyclicSucc i) ∈ H.contactWagonClique (A.core.wagon p) := by
  obtain ⟨x,y,hx,hy,hxp,hyp⟩ := S.split i p hi
  exact ⟨by rw [hx]; exact hxp,by rw [hy]; exact hyp⟩

theorem split_half_sides (i : Fin B.length) (p : P) (hi : S.insert i = some p) :
    ∃ a b : I ⊕ E, a ≠ b ∧ B.vertex i ∈ A.constituent a ∧
      Sum.inr (A.core.wagon p) ∈ A.constituent a ∧
      Sum.inr (A.core.wagon p) ∈ A.constituent b ∧
      B.vertex (cyclicSucc i) ∈ A.constituent b := by
  obtain ⟨x,y,hx,hy,hxp,hyp⟩ := S.split i p hi
  obtain ⟨a,ha,ha'⟩ := A.mixed_incidence_constituent _ x hxp
  obtain ⟨b,hb,hb'⟩ := A.mixed_incidence_constituent _ y hyp
  refine ⟨a,b,?_,by rw [hx]; exact ha,ha',hb',by rw [hy]; exact hb⟩
  intro he
  apply S.not_direct i p hi
  refine ⟨a,by rw [hx]; exact ha,?_⟩
  rw [hy,he]
  exact hb

/-- The only original points in the wagon of a split side are its
two endpoints. -/
theorem split_wagon_trace (hb : B.Bad H.contactClique)
    (i : Fin B.length) (p : P) (hi : S.insert i = some p)
    (j : Fin B.length) (hj : B.vertex j ∈ H.contactWagonClique (A.core.wagon p)) :
    j = i ∨ j = cyclicSucc i := by
  classical
  by_contra h
  push_neg at h
  have hlen : 2 ≤ B.length := by have := B.hlength; omega
  obtain ⟨h0,h1⟩ := S.split_endpoints i p hi
  exact B.bad_no_three hb (Sum.inr (A.core.wagon p))
    (fun he => contactSucc_ne hlen i he.symm) (fun he => h.1 he.symm)
    (fun he => h.2 he.symm) h0 h1 hj

/-- Inserting the chosen wagon cannot repeat an original vertex. -/
theorem split_fresh (hb : B.Bad H.contactClique)
    (i : Fin B.length) (p : P) (hi : S.insert i = some p)
    (j : Fin B.length) : B.vertex j ≠ Sum.inr (A.core.wagon p) := by
  intro he
  have hj : B.vertex j ∈ H.contactWagonClique (A.core.wagon p) := by
    rw [he]
    rfl
  obtain ⟨x,y,hx,hy,_,_⟩ := S.split i p hi
  rcases S.split_wagon_trace hb i p hi j hj with hj | hj
  · rw [hj,hx] at he
    cases he
  · rw [hj,hy] at he
    cases he

/-- Two different split sides cannot insert the same wagon. -/
theorem split_injective (hb : B.Bad H.contactClique)
    (i j : Fin B.length) (p : P)
    (hi : S.insert i = some p) (hj : S.insert j = some p) : i = j := by
  classical
  obtain ⟨h0,h1⟩ := S.split_endpoints j p hj
  have hn : 2 ≤ B.length := by have := B.hlength; omega
  rcases S.split_wagon_trace hb i p hi j h0 with he | he
  · exact he.symm
  · have hs := S.split_wagon_trace hb i p hi (cyclicSucc j) h1
    rw [he] at hs
    rcases hs with hh | hh
    · exact (contactSucc_sq_ne B.hlength i hh).elim
    · exact (contactSucc_ne hn (cyclicSucc i) hh).elim

end SidePlan
end ContactPictureData

namespace ContactPictureCopies
variable {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    {H : OrderOneData U F (I × I₀) R} {A : ContactPictureData D L H}
    (C : ContactPictureCopies A)

noncomputable def sidePlan (B : ContactPolygon U R) (hb : B.IsCycle H.contactClique) :
    A.SidePlan B := by
  classical
  let direct : Fin B.length → Prop := fun i =>
    ∃ a : I ⊕ E, B.vertex i ∈ A.constituent a ∧
      B.vertex (cyclicSucc i) ∈ A.constituent a
  have alt : ∀ i, ¬ direct i → ∃ p : P, ∃ x y : U,
      B.vertex i = Sum.inl x ∧ B.vertex (cyclicSucc i) = Sum.inl y ∧
        x ∈ H.contactWagonCarrier (A.core.wagon p) ∧
        y ∈ H.contactWagonCarrier (A.core.wagon p) := by
    intro i hnd
    rcases C.side_or_subdivide (hb i) with hd | ⟨x,y,p,hx,hy,hxp,hyp⟩
    · exact (hnd hd).elim
    · exact ⟨p,x,y,hx,hy,hxp,hyp⟩
  let ins : Fin B.length → Option P := fun i =>
    if h : direct i then none else some (Classical.choose (alt i h))
  refine {
    insert := ins
    direct := ?_
    split := ?_
    not_direct := ?_
  }
  · intro i hi
    by_contra hn
    simp [ins,hn] at hi
  · intro i p hi
    by_cases hd : direct i
    · simp [ins,hd] at hi
    · have he : Classical.choose (alt i hd) = p := by simpa [ins,hd] using hi
      rw [← he]
      exact Classical.choose_spec (alt i hd)
  · intro i p hi hd
    have h : direct i := hd
    simp [ins,h] at hi

end ContactPictureCopies
end StructuralRamsey.Girth
