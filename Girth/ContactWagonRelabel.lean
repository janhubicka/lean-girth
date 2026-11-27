import Girth.ContactBadCycle

/-! Contact system girth is invariant under bijective relabelling of
the wagon classes, without identifying different labels that happen
to have equal carriers. This permits a single-edge bottom cut to be
represented literally by its edge labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P R : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I P) (e : P ≃ R)

def relabelWagons : OrderOneData V E I R where
  edgeCarrier := D.edgeCarrier
  copyCarrier := D.copyCarrier
  copyEdges := D.copyEdges
  parent := e ∘ D.parent

theorem relabel_carrier (p : P) :
    (D.relabelWagons e).contactWagonCarrier (e p) = D.contactWagonCarrier p := by
  ext x
  constructor
  · rintro ⟨f,hf,hx⟩
    exact ⟨f,e.injective hf,hx⟩
  · rintro ⟨f,hf,hx⟩
    exact ⟨f,congrArg e hf,hx⟩

theorem relabel_meets (i : I) (p : P) :
    (D.relabelWagons e).contactMeets i (e p) ↔ D.contactMeets i p := by
  constructor
  · rintro ⟨f,hf,hp⟩
    exact ⟨f,hf,e.injective hp⟩
  · rintro ⟨f,hf,hp⟩
    exact ⟨f,hf,congrArg e hp⟩

/-- The contact and generating-clique indices are both relabelled
bijectively, with exact membership. -/
theorem relabel_clique (a : I ⊕ P) (z : V ⊕ P) :
    (Equiv.sumCongr (Equiv.refl V) e) z ∈
      (D.relabelWagons e).contactClique ((Equiv.sumCongr (Equiv.refl I) e) a) ↔
      z ∈ D.contactClique a := by
  cases a with
  | inl i =>
    cases z with
    | inl x => rfl
    | inr p => exact D.relabel_meets e i p
  | inr p =>
    cases z with
    | inl x =>
      change x ∈ (D.relabelWagons e).contactWagonCarrier (e p) ↔
        x ∈ D.contactWagonCarrier p
      rw [D.relabel_carrier e]
    | inr r =>
      change e r = e p ↔ r = p
      exact ⟨fun h => e.injective h,fun h => congrArg e h⟩

theorem relabel_adj (x y : V ⊕ P) :
    contactAdjacent (D.relabelWagons e).contactClique
      ((Equiv.sumCongr (Equiv.refl V) e) x) ((Equiv.sumCongr (Equiv.refl V) e) y) ↔
      contactAdjacent D.contactClique x y := by
  let f := Equiv.sumCongr (Equiv.refl V) e
  let g := Equiv.sumCongr (Equiv.refl I) e
  constructor
  · rintro ⟨hne,a,hx,hy⟩
    obtain ⟨b,rfl⟩ := g.surjective a
    exact ⟨fun h => hne (congrArg f h),b,
      (D.relabel_clique e b x).mp hx,(D.relabel_clique e b y).mp hy⟩
  · rintro ⟨hne,b,hx,hy⟩
    exact ⟨fun h => hne (f.injective h),g b,
      (D.relabel_clique e b x).mpr hx,(D.relabel_clique e b y).mpr hy⟩

theorem relabel_linear (h : D.ContactLinear) :
    (D.relabelWagons e).ContactLinear := by
  refine ⟨h.1,?_⟩
  intro p r hne
  obtain ⟨p,rfl⟩ := e.surjective p
  obtain ⟨r,rfl⟩ := e.surjective r
  rw [D.relabel_carrier e,D.relabel_carrier e]
  exact h.2 p r (fun he => hne (congrArg e he))

theorem relabel_g1 (h : D.ContactG1) :
    (D.relabelWagons e).ContactG1 := by
  refine ⟨h.edge_subset,h.strong,?_⟩
  intro i p htrigger x hx hxp
  obtain ⟨p,rfl⟩ := e.surjective p
  have ht : D.contactMeets i p ∨ (D.copyCarrier i ∩ D.contactWagonCarrier p).Nontrivial := by
    rcases htrigger with hm | hn
    · exact Or.inl ((D.relabel_meets e i p).mp hm)
    · right
      change (D.copyCarrier i ∩ (D.relabelWagons e).contactWagonCarrier (e p)).Nontrivial at hn
      rw [D.relabel_carrier e] at hn
      exact hn
  rw [D.relabel_carrier e] at hxp
  obtain ⟨f,hf,hp,hxf⟩ := h.bridge i p ht x hx hxp
  exact ⟨f,hf,congrArg e hp,hxf⟩

theorem relabel_g2 (h : D.ContactG2) :
    (D.relabelWagons e).ContactG2 := by
  let f := Equiv.sumCongr (Equiv.refl V) e
  intro i j hij hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  obtain ⟨u,rfl⟩ := f.surjective x
  obtain ⟨v,rfl⟩ := f.surjective y
  have hm (k : I) (z : V ⊕ P) :
      f z ∈ (D.relabelWagons e).contactCopyClique k ↔ z ∈ D.contactCopyClique k :=
    D.relabel_clique e (Sum.inl k) z
  obtain ⟨p,hp⟩ := h i j hij
    ⟨u,⟨(hm i u).mp hx.1,(hm j u).mp hx.2⟩,
      v,⟨(hm i v).mp hy.1,(hm j v).mp hy.2⟩,fun he => hxy (congrArg f he)⟩
  refine ⟨e p,?_⟩
  intro z hz
  obtain ⟨w,rfl⟩ := f.surjective z
  exact (D.relabel_clique e (Sum.inr p) w).mpr
    (hp ⟨(hm i w).mp hz.1,(hm j w).mp hz.2⟩)

theorem relabel_g3 {q : ℕ} (h : LabelledGirthGT D.contactWagonCarrier q) :
    LabelledGirthGT (D.relabelWagons e).contactWagonCarrier q := by
  refine labelledGirthGT_of_injective_shrinking D.contactWagonCarrier
    (D.relabelWagons e).contactWagonCarrier e.symm e.symm.injective ?_ q h
  intro p
  obtain ⟨r,rfl⟩ := e.surjective p
  rw [e.symm_apply_apply,D.relabel_carrier e]

/-- Map a bad polygon back through the relabelling; weights, covered
cliques and chords are all preserved. -/
theorem relabel_g4 {q : ℕ} (h : ContactG4 D.contactClique q) :
    ContactG4 (D.relabelWagons e).contactClique q := by
  classical
  apply contactG4_of_no_bad
  intro C hw hb
  let f := Equiv.sumCongr (Equiv.refl V) e
  let g := Equiv.sumCongr (Equiv.refl I) e
  let B : ContactPolygon V P := {
    length := C.length
    hlength := C.hlength
    vertex := fun i => f.symm (C.vertex i)
    vertex_injective := f.symm.injective.comp C.vertex_injective
  }
  have hv : ∀ i, f (B.vertex i) = C.vertex i :=
    fun i => f.apply_symm_apply (C.vertex i)
  have hc : B.IsCycle D.contactClique := by
    intro i
    apply (D.relabel_adj e _ _).mp
    change contactAdjacent (D.relabelWagons e).contactClique
      (f (B.vertex i)) (f (B.vertex (cyclicSucc i)))
    rw [hv,hv]
    exact hb.1 i
  have he : B.twiceWeight = C.twiceWeight := by
    unfold ContactPolygon.twiceWeight
    apply Finset.sum_congr rfl
    intro i _
    change contactWeight (B.vertex i) (B.vertex (cyclicSucc i)) =
      contactWeight (C.vertex i) (C.vertex (cyclicSucc i))
    have hweight (x y : V ⊕ P) : contactWeight (f x) (f y) = contactWeight x y := by
      cases x <;> cases y <;> rfl
    rw [← hv i,← hv (cyclicSucc i),hweight]
  rcases contactSharedChordBound_of_G4 h B hc (by rw [he]; exact hw) with hcover | hchord
  · obtain ⟨a,ha⟩ := hcover
    apply hb.2.1
    refine ⟨g a,?_⟩
    intro i
    rw [← hv i]
    exact (D.relabel_clique e a (B.vertex i)).mpr (ha i)
  · obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := hchord
    have hAdj : contactAdjacent D.contactClique (B.vertex i) (B.vertex j) :=
      ⟨fun he => hnc.1 (B.vertex_injective he),a,hia,hja⟩
    apply hb.2.2
    refine ⟨i,j,hnc,?_⟩
    rw [← hv i,← hv j]
    exact (D.relabel_adj e _ _).mpr hAdj

theorem relabel_systemGirth {q : ℕ} (h : D.ContactSystemGirthGT q) :
    (D.relabelWagons e).ContactSystemGirthGT q :=
  ⟨D.relabel_linear e h.linear,D.relabel_g1 e h.g1,D.relabel_g2 e h.g2,
    D.relabel_g3 e h.g3,D.relabel_g4 e h.g4⟩

theorem relabel_inverse :
    (D.relabelWagons e).relabelWagons e.symm = D := by
  cases D with
  | mk ec cc ce p =>
    change OrderOneData.mk ec cc ce (e.symm ∘ (e ∘ p)) = OrderOneData.mk ec cc ce p
    have he : e.symm ∘ (e ∘ p) = p := by
      funext f
      exact e.symm_apply_apply (p f)
    rw [he]

theorem relabel_systemGirth_iff {q : ℕ} :
    (D.relabelWagons e).ContactSystemGirthGT q ↔ D.ContactSystemGirthGT q := by
  constructor
  · intro h
    have h' := (D.relabelWagons e).relabel_systemGirth e.symm h
    rw [D.relabel_inverse e] at h'
    exact h'
  · exact D.relabel_systemGirth e

end OrderOneData
end StructuralRamsey.Girth
