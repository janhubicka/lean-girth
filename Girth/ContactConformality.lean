import Girth.ContactSelectedCycles
import Mathlib.Data.Fin.VecNotation

/-! Conformality of the small selected bottom family. A minimal
uncovered clique cannot have size three by the sparse-polygon
obstruction. A larger minimal uncovered clique gives a Berge
triangle of three actual ambient edges, using only its four
deletion witnesses. -/

namespace StructuralRamsey.Girth

universe v
variable {V E I J : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)

theorem zero_selected_triangle_covered [Fintype J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q)
    (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hab : ∃ a : J, x ∈ D.carrier (sel a) ∧ y ∈ D.carrier (sel a))
    (hbc : ∃ a : J, y ∈ D.carrier (sel a) ∧ z ∈ D.carrier (sel a))
    (hca : ∃ a : J, z ∈ D.carrier (sel a) ∧ x ∈ D.carrier (sel a)) :
    ∃ a : J, x ∈ D.carrier (sel a) ∧ y ∈ D.carrier (sel a) ∧ z ∈ D.carrier (sel a) := by
  classical
  let K : J → Set (V ⊕ E) := fun a => D.zeroRealClique (sel a)
  have hadj (u w : V) (hne : u ≠ w)
      (he : ∃ a : J, u ∈ D.carrier (sel a) ∧ w ∈ D.carrier (sel a)) :
      contactAdjacent K (Sum.inl u) (Sum.inl w) := by
    obtain ⟨a,hu,hw⟩ := he
    exact ⟨fun eq => hne (Sum.inl.inj eq),a,
      (D.zeroRealClique_mem _ _).mpr hu,(D.zeroRealClique_mem _ _).mpr hw⟩
  let C : ContactPolygon V E := {
    length := 3
    hlength := by omega
    vertex := ![Sum.inl x,Sum.inl y,Sum.inl z]
    vertex_injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  }
  have hc : C.IsCycle K := by
    intro i
    fin_cases i
    · simpa [C,cyclicSucc] using hadj x y hxy hab
    · simpa [C,cyclicSucc] using hadj y z hyz hbc
    · simpa [C,cyclicSucc] using hadj z x hzx hca
  have hw : C.twiceWeight ≤ 2*3 := by
    simp [ContactPolygon.twiceWeight,C,Fin.sum_univ_succ,cyclicSucc,
      contactWeight,contactKind,twiceOccurrenceWeight]
  obtain ⟨a,ha⟩ := ((D.zero_selected_real_g4 h0 h sel hcard 3) C hc hw).1 rfl
  exact ⟨a,(D.zeroRealClique_mem _ _).mp (ha 0),
    (D.zeroRealClique_mem _ _).mp (ha 1),(D.zeroRealClique_mem _ _).mp (ha 2)⟩

/-- Three distinct actual ambient edges supporting the three pairs
of three distinct vertices give a genuine labelled Berge triangle. -/
theorem zero_forbid_three_edges {q : ℕ} (h0 : ∀ e, D.parent e = e)
    (hg : LabelledGirthGT D.contactWagonCarrier q) (hq : 3 ≤ q)
    (a b c : E) (x y z : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hax : x ∈ D.edgeCarrier a) (hay : y ∈ D.edgeCarrier a)
    (hby : y ∈ D.edgeCarrier b) (hbz : z ∈ D.edgeCarrier b)
    (hcz : z ∈ D.edgeCarrier c) (hcx : x ∈ D.edgeCarrier c) : False := by
  have hmem (e : E) (u : V) (hu : u ∈ D.edgeCarrier e) :
      u ∈ D.contactWagonCarrier e := ⟨e,h0 e,hu⟩
  let C : LabelledBergeCycle D.contactWagonCarrier := {
    length := 3
    hlength := by omega
    label := ![a,b,c]
    vertex := ![y,z,x]
    label_injective := by
      intro i j he
      fin_cases i <;> fin_cases j <;> simp_all
    vertex_injective := by
      intro i j he
      fin_cases i <;> fin_cases j <;> simp_all
    left_mem := by
      intro i
      fin_cases i
      · exact hmem a y hay
      · exact hmem b z hbz
      · exact hmem c x hcx
    right_mem := by
      intro i
      fin_cases i
      · simpa [cyclicSucc] using hmem b y hby
      · simpa [cyclicSucc] using hmem c z hcz
      · simpa [cyclicSucc] using hmem a x hax
  }
  exact hg ⟨C,hq⟩

/-- A finite set whose four one-point-deletion witnesses omit their
respective deleted vertices cannot have all these witnesses in a
linear bottom system of girth > q, q ≥ 3. -/
theorem zero_four_deletions_impossible {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q) (hq : 3 ≤ q)
    (s : Finset V) (x y z w : V)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hw : w ∈ s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (a b c d : I ⊕ E)
    (ha : ∀ u ∈ s, u ≠ x → u ∈ D.carrier a)
    (hb : ∀ u ∈ s, u ≠ y → u ∈ D.carrier b)
    (hc : ∀ u ∈ s, u ≠ z → u ∈ D.carrier c)
    (hd : ∀ u ∈ s, u ≠ w → u ∈ D.carrier d)
    (hna : x ∉ D.carrier a) (hnb : y ∉ D.carrier b)
    (hnc : z ∉ D.carrier c) (hnd : w ∉ D.carrier d) : False := by
  have edge_of_inter (b' : I ⊕ E) (hne : a ≠ b')
      (u v : V) (huv : u ≠ v)
      (hua : u ∈ D.carrier a) (hva : v ∈ D.carrier a)
      (hub : u ∈ D.carrier b') (hvb : v ∈ D.carrier b') :
      ∃ e, e ∈ D.edges a ∧ e ∈ D.edges b' ∧
        u ∈ D.edgeCarrier e ∧ v ∈ D.edgeCarrier e := by
    rcases D.zero_pairwise_allowed h0 h.linear h.g1 h.g2 a b' hne with hs | ⟨e,he,hf,heq⟩
    · exact (huv (hs ⟨hua,hub⟩ ⟨hva,hvb⟩)).elim
    · have hu : u ∈ D.carrier a ∩ D.carrier b' := ⟨hua,hub⟩
      have hv : v ∈ D.carrier a ∩ D.carrier b' := ⟨hva,hvb⟩
      rw [heq] at hu hv
      exact ⟨e,he,hf,hu,hv⟩
  have hab : a ≠ b := by intro he; exact hna (by rw [he]; exact hb x hx hxy)
  have hac : a ≠ c := by intro he; exact hna (by rw [he]; exact hc x hx hxz)
  have had : a ≠ d := by intro he; exact hna (by rw [he]; exact hd x hx hxw)
  obtain ⟨e,he₁,he₂,hez,hew⟩ := edge_of_inter b hab z w hzw
    (ha z hz hxz.symm) (ha w hw hxw.symm) (hb z hz hyz.symm) (hb w hw hyw.symm)
  obtain ⟨f,hf₁,hf₂,hfy,hfw⟩ := edge_of_inter c hac y w hyw
    (ha y hy hxy.symm) (ha w hw hxw.symm) (hc y hy hyz) (hc w hw hzw.symm)
  obtain ⟨g,hg₁,hg₂,hgy,hgz⟩ := edge_of_inter d had y z hyz
    (ha y hy hxy.symm) (ha z hz hxz.symm) (hd y hy hyw) (hd z hz hzw)
  have hef : e ≠ f := by
    intro heq
    apply hnb
    apply D.zero_piece_edge_subset h.g1 b e he₂
    rw [heq]
    exact hfy
  have hfg : f ≠ g := by
    intro heq
    apply hnc
    apply D.zero_piece_edge_subset h.g1 c f hf₂
    rw [heq]
    exact hgz
  have hge : g ≠ e := by
    intro heq
    apply hnd
    apply D.zero_piece_edge_subset h.g1 d g hg₂
    rw [heq]
    exact hew
  exact D.zero_forbid_three_edges h0 h.g3 hq e f g z w y hef hfg hge
    hzw hyw.symm hyz hez hew hfw hfy hgy hgz

/-- The selected real-vertex two-section is conformal. The finite
clique formulation includes explicitly that singleton cliques occur
in at least one selected carrier, so isolated unused ambient vertices
do not create a false counterexample. -/
theorem zero_selected_conformal [Fintype J] {q : ℕ}
    (h0 : ∀ e, D.parent e = e) (h : D.ContactSystemGirthGT q)
    (sel : J → I ⊕ E) (hcard : Fintype.card J ≤ q)
    (s : Finset V) (hne : s.Nonempty)
    (hsingle : ∀ x ∈ s, ∃ a : J, x ∈ D.carrier (sel a))
    (hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ∃ a : J, x ∈ D.carrier (sel a) ∧ y ∈ D.carrier (sel a)) :
    ∃ a : J, (↑s : Set V) ⊆ D.carrier (sel a) := by
  classical
  by_contra hnot
  let Bad : ℕ → Prop := fun n => ∃ t : Finset V, t ⊆ s ∧ t.card = n ∧
    ¬ ∃ a : J, (↑t : Set V) ⊆ D.carrier (sel a)
  have hExists : ∃ n, Bad n := ⟨s.card,s,Finset.Subset.rfl,rfl,hnot⟩
  obtain ⟨t,ht,htcard,htbad⟩ := Nat.find_spec hExists
  have hdel : ∀ x : V, x ∈ t → ∃ a : J,
      (∀ u ∈ t, u ≠ x → u ∈ D.carrier (sel a)) ∧ x ∉ D.carrier (sel a) := by
    intro x hx
    have hex : ∃ a : J, (↑(t.erase x) : Set V) ⊆ D.carrier (sel a) := by
      by_contra hn
      have hmin := Nat.find_min' hExists
        (show Bad (t.erase x).card from ⟨t.erase x,
          (Finset.erase_subset _ _).trans ht,rfl,hn⟩)
      have hl := Finset.card_erase_lt_of_mem hx
      omega
    obtain ⟨a,ha⟩ := hex
    refine ⟨a,fun u hu hux => ha (Finset.mem_erase.mpr ⟨hux,hu⟩),?_⟩
    intro hxa
    apply htbad
    refine ⟨a,?_⟩
    intro u hu
    by_cases he : u = x
    · simpa only [he] using hxa
    · exact ha (Finset.mem_erase.mpr ⟨he,hu⟩)
  have hnonempty : t.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨a,ha⟩ := hsingle x hx
    by_contra hn
    have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact htbad ⟨a,by simp [he]⟩
  have htwo : 2 < t.card := by
    by_contra hn
    have hle : t.card ≤ 2 := by omega
    obtain ⟨x,hx⟩ := hnonempty
    by_cases hs : t = {x}
    · obtain ⟨a,ha⟩ := hsingle x (ht hx)
      exact htbad ⟨a,by simpa [hs] using ha⟩
    · have hex : (t.erase x).Nonempty := by
        by_contra hn'
        have he : t.erase x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn'
        exact hs (by rw [← Finset.insert_erase hx,he]; simp)
      obtain ⟨y,hy⟩ := hex
      have hy' := (Finset.mem_erase.mp hy).2
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      have he : ({x,y} : Finset V) = t := by
        apply Finset.eq_of_subset_of_card_le
        · intro u hu
          simp only [Finset.mem_insert,Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hx
          · exact hy'
        · rw [Finset.card_pair hxy]
          exact hle
      obtain ⟨a,ha,ha'⟩ := hpair x (ht hx) y (ht hy') hxy
      exact htbad ⟨a,by rw [← he]; simp [ha,ha']⟩
  have hbudget : t.card ≤ q := by
    have hx : ∀ x : {x // x ∈ t}, ∃ a : J,
        (∀ u ∈ t, u ≠ x.val → u ∈ D.carrier (sel a)) ∧
          x.val ∉ D.carrier (sel a) := fun x => hdel x.val x.property
    choose own hown using hx
    have hinj : Function.Injective own := by
      intro x y he
      by_contra hn
      have hne : x.val ≠ y.val := fun he' => hn (Subtype.ext he')
      apply (hown x).2
      rw [he]
      exact (hown y).1 x.val x.property hne
    have hc := Fintype.card_le_of_injective own hinj
    simpa using hc.trans hcard
  obtain ⟨x,hx⟩ := hnonempty
  have h2ne : (t.erase x).Nonempty := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hx]; omega)
  obtain ⟨y,hy⟩ := h2ne
  have hy' := (Finset.mem_erase.mp hy).2
  have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
  have h3ne : ((t.erase x).erase y).Nonempty := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hy,Finset.card_erase_of_mem hx]; omega)
  obtain ⟨z,hz⟩ := h3ne
  have hz' := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  have hxz : x ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1.symm
  have hyz : y ≠ z := (Finset.mem_erase.mp hz).1.symm
  by_cases hthree : t.card = 3
  · have hset : ({x,y,z} : Finset V) = t := by
      apply Finset.eq_of_subset_of_card_le
      · intro u hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hx
        · exact hy'
        · exact hz'
      · have hnotmem : x ∉ ({y,z} : Finset V) := by simp [hxy,hxz]
        rw [Finset.card_insert_of_notMem hnotmem,Finset.card_pair hyz,hthree]
    obtain ⟨a,ha,hb,hc⟩ := D.zero_selected_triangle_covered h0 h sel hcard
      x y z hxy hyz hxz.symm
      (hpair x (ht hx) y (ht hy') hxy)
      (hpair y (ht hy') z (ht hz') hyz)
      (hpair z (ht hz') x (ht hx) hxz.symm)
    exact htbad ⟨a,by rw [← hset]; simp [ha,hb,hc]⟩
  · have h4ne : (((t.erase x).erase y).erase z).Nonempty := Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem hz,Finset.card_erase_of_mem hy,
        Finset.card_erase_of_mem hx]; omega)
    obtain ⟨w,hw⟩ := h4ne
    have hw₁ := (Finset.mem_erase.mp hw).2
    have hw₂ := (Finset.mem_erase.mp hw₁).2
    have hw' := (Finset.mem_erase.mp hw₂).2
    have hxw : x ≠ w := (Finset.mem_erase.mp hw₂).1.symm
    have hyw : y ≠ w := (Finset.mem_erase.mp hw₁).1.symm
    have hzw : z ≠ w := (Finset.mem_erase.mp hw).1.symm
    obtain ⟨a,ha,hna⟩ := hdel x hx
    obtain ⟨b,hb,hnb⟩ := hdel y hy'
    obtain ⟨c,hc,hnc⟩ := hdel z hz'
    obtain ⟨d,hd,hnd⟩ := hdel w hw'
    exact D.zero_four_deletions_impossible h0 h (by omega) t x y z w
      hx hy' hz' hw' hxy hxz hxw hyz hyw hzw
      (sel a) (sel b) (sel c) (sel d) ha hb hc hd hna hnb hnc hnd

end OrderOneData
end StructuralRamsey.Girth
