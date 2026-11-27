import Girth.ContactBadCycle

/-! Level-zero mixed forests: the common-pair and short-cycle kernels.
At this cut each wagon is one edge. A covered side of a short cycle,
if its third vertex lies outside the designated side owner, forces
an actual hyperedge of that owner. This turns a bad cycle of pieces
into a labelled Berge cycle, without any acceptable-cycle machinery. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)

theorem zero_wagonCarrier_eq (h0 : ∀ e, D.parent e = e) (p : E) :
    D.contactWagonCarrier p = D.edgeCarrier p := by
  ext x
  constructor
  · rintro ⟨e,he,hx⟩
    have hep : e = p := (h0 e).symm.trans he
    simpa only [hep] using hx
  · intro hx
    exact ⟨p,h0 p,hx⟩

theorem zero_piece_contact (h0 : ∀ e, D.parent e = e)
    (a : I ⊕ E) (x : V) :
    (Sum.inl x : V ⊕ E) ∈ D.contactClique a ↔ x ∈ D.carrier a := by
  cases a with
  | inl i => rfl
  | inr e =>
    change x ∈ D.contactWagonCarrier e ↔ x ∈ D.edgeCarrier e
    rw [D.zero_wagonCarrier_eq h0]

theorem zero_piece_edge_subset (h1 : D.ContactG1) (a : I ⊕ E) (e : E)
    (he : e ∈ D.edges a) : D.edgeCarrier e ⊆ D.carrier a := by
  cases a with
  | inl i => exact h1.edge_subset i e he
  | inr f =>
    have hef : e = f := he
    subst e
    exact Set.Subset.rfl

/-- Two different generating cliques covering the same real pair
force an edge of the first piece containing that pair. -/
theorem zero_pair_edge_of_distinct_cliques
    (h0 : ∀ e, D.parent e = e) (h1 : D.ContactG1) (h2 : D.ContactG2)
    (a b : I ⊕ E) (hab : a ≠ b) (x y : V) (hxy : x ≠ y)
    (hxa : x ∈ D.carrier a) (hya : y ∈ D.carrier a)
    (hxb : (Sum.inl x : V ⊕ E) ∈ D.contactClique b)
    (hyb : (Sum.inl y : V ⊕ E) ∈ D.contactClique b) :
    ∃ e, e ∈ D.edges a ∧ x ∈ D.edgeCarrier e ∧ y ∈ D.edgeCarrier e := by
  cases a with
  | inr e => exact ⟨e,rfl,hxa,hya⟩
  | inl i =>
    obtain ⟨e,hxe,hye⟩ := D.contact_shared_pair_in_wagon h2 hab
      (fun he => hxy (Sum.inl.inj he)) hxa hya hxb hyb
    have hx : x ∈ D.edgeCarrier e := by
      change x ∈ D.contactWagonCarrier e at hxe
      rw [D.zero_wagonCarrier_eq h0 e] at hxe
      exact hxe
    have hy : y ∈ D.edgeCarrier e := by
      change y ∈ D.contactWagonCarrier e at hye
      rw [D.zero_wagonCarrier_eq h0 e] at hye
      exact hye
    exact ⟨e,h1.strong i e ⟨x,⟨hx,hxa⟩,y,⟨hy,hya⟩,hxy⟩,hx,hy⟩

/-- At level zero, all two-point intersections of different pieces
are actual common edges. This includes edge copies and repeated
carrier sets with distinct indices. -/
theorem zero_pairwise_allowed
    (h0 : ∀ e, D.parent e = e) (hlin : D.ContactLinear)
    (h1 : D.ContactG1) (h2 : D.ContactG2)
    (a b : I ⊕ E) (hab : a ≠ b) :
    (D.carrier a ∩ D.carrier b).Subsingleton ∨
      ∃ e, e ∈ D.edges a ∧ e ∈ D.edges b ∧
        D.carrier a ∩ D.carrier b = D.edgeCarrier e := by
  classical
  by_cases hs : (D.carrier a ∩ D.carrier b).Subsingleton
  · exact Or.inl hs
  · right
    obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hs
    have full : ∃ p, D.contactClique a ∩ D.contactClique b ⊆ D.contactWagonClique p := by
      cases a with
      | inr p => exact ⟨p,fun _ hz => hz.1⟩
      | inl i =>
        cases b with
        | inr p => exact ⟨p,fun _ hz => hz.2⟩
        | inl j =>
          exact h2 i j (fun he => hab (congrArg Sum.inl he))
            ⟨Sum.inl x,⟨hx.1,hx.2⟩,Sum.inl y,⟨hy.1,hy.2⟩,
              fun he => hxy (Sum.inl.inj he)⟩
    obtain ⟨e,he⟩ := full
    have hsub : D.carrier a ∩ D.carrier b ⊆ D.edgeCarrier e := by
      intro z hz
      have hze : (Sum.inl z : V ⊕ E) ∈ D.contactWagonClique e :=
        he ⟨(D.zero_piece_contact h0 a z).mpr hz.1,
          (D.zero_piece_contact h0 b z).mpr hz.2⟩
      change z ∈ D.contactWagonCarrier e at hze
      rw [D.zero_wagonCarrier_eq h0] at hze
      exact hze
    have in_piece (c : I ⊕ E) (hxc : x ∈ D.carrier c)
        (hyc : y ∈ D.carrier c) : e ∈ D.edges c := by
      cases c with
      | inl i =>
        exact h1.strong i e ⟨x,⟨hsub hx,hxc⟩,y,⟨hsub hy,hyc⟩,hxy⟩
      | inr f =>
        change e = f
        by_contra hne
        exact hxy (hlin.1 e f hne ⟨hsub hx,hxc⟩ ⟨hsub hy,hyc⟩)
    have hea := in_piece a hx.1 hy.1
    have heb := in_piece b hx.2 hy.2
    exact ⟨e,hea,heb,Set.Subset.antisymm hsub
      (fun z hz => ⟨D.zero_piece_edge_subset h1 a e hea hz,
                    D.zero_piece_edge_subset h1 b e heb hz⟩)⟩

/-- A short cycle with sides in pieces containing no third cycle
vertex is impossible. In the forest proof, chordlessness of the
selected two-section (or an uncovered triangle) supplies precisely
this no-third-vertex condition. -/
theorem zero_no_sparse_polygon {q n : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (hn : 3 ≤ n) (hq : n ≤ q)
    (vtx : Fin n → V) (hvtx : Function.Injective vtx)
    (owner : Fin n → I ⊕ E)
    (left : ∀ i, vtx i ∈ D.carrier (owner i))
    (right : ∀ i, vtx (cyclicSucc i) ∈ D.carrier (owner i))
    (no_third : ∀ i j, j ≠ i → j ≠ cyclicSucc i →
      vtx j ∉ D.carrier (owner i)) : False := by
  classical
  let C : ContactPolygon V E := {
    length := n
    hlength := hn
    vertex := fun i => Sum.inl (vtx i)
    vertex_injective := fun _ _ he => hvtx (Sum.inl.inj he)
  }
  have hnC : 2 ≤ C.length := by change 2 ≤ n; omega
  have hc : C.IsCycle D.contactClique := by
    intro i
    exact ⟨fun he => contactSucc_ne hnC i (hvtx (Sum.inl.inj he)).symm,
      owner i,(D.zero_piece_contact h0 (owner i) (vtx i)).mpr (left i),
      (D.zero_piece_contact h0 (owner i) (vtx (cyclicSucc i))).mpr (right i)⟩
  have hw : C.twiceWeight ≤ 2*q := by
    have he : C.twiceWeight = 2*n := by
      simp [ContactPolygon.twiceWeight,C,contactWeight,contactKind,
        twiceOccurrenceWeight,Nat.mul_comm]
    omega
  have hactual : ∀ i : Fin n, ∃ e,
      e ∈ D.edges (owner i) ∧ vtx i ∈ D.edgeCarrier e ∧
        vtx (cyclicSucc i) ∈ D.edgeCarrier e := by
    intro i
    obtain ⟨j,hji,hjs,a,hxa,hya,hza⟩ := contactCoveredSide_of_G4 h.g4 C hc hw i
    have hne : owner i ≠ a := by
      intro he
      apply no_third i j hji hjs
      exact (D.zero_piece_contact h0 (owner i) (vtx j)).mp
        (by simpa only [he] using hza)
    exact D.zero_pair_edge_of_distinct_cliques h0 h.g1 h.g2 (owner i) a hne
      (vtx i) (vtx (cyclicSucc i))
      (fun he => contactSucc_ne (by omega) i (hvtx he).symm)
      (left i) (right i) hxa hya
  choose edge hEdge using hactual
  have hInj : Function.Injective edge := by
    intro i j he
    by_contra hne
    have hjmem : vtx j ∈ D.carrier (owner i) :=
      D.zero_piece_edge_subset h.g1 (owner i) (edge i) (hEdge i).1
        (by rw [he]; exact (hEdge j).2.1)
    have hjs : j = cyclicSucc i := by
      by_contra hn'
      exact no_third i j (fun h' => hne h'.symm) hn' hjmem
    have hsmem : vtx (cyclicSucc j) ∈ D.carrier (owner i) :=
      D.zero_piece_edge_subset h.g1 (owner i) (edge i) (hEdge i).1
        (by rw [he]; exact (hEdge j).2.2)
    have hsi : cyclicSucc j ≠ i := by
      rw [hjs]
      exact contactSucc_sq_ne hn i
    have hss : cyclicSucc j ≠ cyclicSucc i := fun he' =>
      hne ((ContactCyclicRestriction.contactCyclicSucc_injective he').symm)
    exact no_third i (cyclicSucc j) hsi hss hsmem
  let B : LabelledBergeCycle D.contactWagonCarrier := {
    length := n
    hlength := by omega
    label := edge
    vertex := fun i => vtx (cyclicSucc i)
    label_injective := hInj
    vertex_injective := hvtx.comp ContactCyclicRestriction.contactCyclicSucc_injective
    left_mem := by
      intro i
      rw [D.zero_wagonCarrier_eq h0]
      exact (hEdge i).2.2
    right_mem := by
      intro i
      rw [D.zero_wagonCarrier_eq h0]
      exact (hEdge (cyclicSucc i)).2.1
  }
  exact h.g3 ⟨B,hq⟩

end OrderOneData
end StructuralRamsey.Girth
