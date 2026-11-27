import Girth.ContactChordalPaths

/-! Minimal vertex separators in a chordal graph are cliques.
All separator and component constructions are actual finite sets
or reachability classes. In particular the two induced paths used
to contradict chordality are constructed from minimality. -/

namespace StructuralRamsey.Girth
universe v
variable {W : Type v}

def contactGraphOn (G : SimpleGraph W) (U : Set W) : SimpleGraph W where
  Adj x y := G.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := {symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩}
  loopless := {irrefl := fun _ h => h.1.ne rfl}

theorem contactGraphOn_le (G : SimpleGraph W) (U : Set W) :
    contactGraphOn G U ≤ G := fun _ _ h => h.1

theorem contactGraphOn_mono (G : SimpleGraph W) {U S : Set W}
    (h : U ⊆ S) : contactGraphOn G U ≤ contactGraphOn G S :=
  fun _ _ he => ⟨he.1,h he.2.1,h he.2.2⟩

/-- Reachability cannot leave a set closed under all edges. -/
theorem contact_reachable_closed {G : SimpleGraph W} {U : Set W}
    (hU : ∀ x y, x ∈ U → G.Adj x y → y ∈ U)
    {a b : W} (ha : a ∈ U) (hab : G.Reachable a b) : b ∈ U := by
  have aux : ∀ {x y : W}, (p : G.Walk x y) → x ∈ U → y ∈ U := by
    intro x y p
    induction p with
    | nil => exact fun hx => hx
    | @cons x z y hxz p ih =>
      intro hx
      exact ih (hU x z hx hxz)
  obtain ⟨p⟩ := hab
  exact aux p ha

theorem contact_reachable_restrict_closed {G : SimpleGraph W} {U : Set W}
    (hU : ∀ x y, x ∈ U → G.Adj x y → y ∈ U)
    {a b : W} (ha : a ∈ U) (hab : G.Reachable a b) :
    (contactGraphOn G U).Reachable a b := by
  have aux : ∀ {x y : W}, (p : G.Walk x y) → x ∈ U →
      (contactGraphOn G U).Reachable x y := by
    intro x y p
    induction p with
    | nil => exact fun _ => SimpleGraph.Reachable.refl _
    | @cons x z y hxz p ih =>
      intro hx
      have hz := hU x z hx hxz
      exact (show (contactGraphOn G U).Adj x z from ⟨hxz,hx,hz⟩).reachable.trans
        (ih hz)
  obtain ⟨p⟩ := hab
  exact aux p ha

def contactComponent (G : SimpleGraph W) (U : Set W) (a : W) : Set W :=
  {x | x ∈ U ∧ (contactGraphOn G U).Reachable a x}

namespace contactComponent

theorem root {G : SimpleGraph W} {U : Set W} {a : W} (ha : a ∈ U) :
    a ∈ contactComponent G U a := ⟨ha,SimpleGraph.Reachable.refl _⟩

theorem closed {G : SimpleGraph W} {U : Set W} {a x y : W}
    (hx : x ∈ contactComponent G U a) (hy : y ∈ U) (h : G.Adj x y) :
    y ∈ contactComponent G U a :=
  ⟨hy,hx.2.trans (show (contactGraphOn G U).Adj x y from ⟨h,hx.1,hy⟩).reachable⟩

theorem disjoint {G : SimpleGraph W} {U : Set W} {a b : W}
    (h : ¬ (contactGraphOn G U).Reachable a b) :
    Disjoint (contactComponent G U a) (contactComponent G U b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact h (hx.2.trans hy.2.symm)

theorem no_cross {G : SimpleGraph W} {U : Set W} {a b x y : W}
    (h : ¬ (contactGraphOn G U).Reachable a b)
    (hx : x ∈ contactComponent G U a) (hy : y ∈ contactComponent G U b) :
    ¬ G.Adj x y := by
  intro he
  exact h ((closed hx hy.1 he).2.trans hy.2.symm)

/-- The actual component is connected using only its own vertices. -/
theorem reachable_inside {G : SimpleGraph W} {U : Set W} {a x y : W}
    (ha : a ∈ U) (hx : x ∈ contactComponent G U a)
    (hy : y ∈ contactComponent G U a) :
    (contactGraphOn G (contactComponent G U a)).Reachable x y := by
  let L := contactComponent G U a
  let G' := contactGraphOn G U
  have hclosed : ∀ u w, u ∈ L → G'.Adj u w → w ∈ L :=
    fun _ _ hu he => closed hu he.2.2 he.1
  have hroot : a ∈ L := root ha
  have hx' := contact_reachable_restrict_closed hclosed hroot hx.2
  have hy' := contact_reachable_restrict_closed hclosed hroot hy.2
  have hm : contactGraphOn G' L ≤ contactGraphOn G L :=
    fun _ _ he => ⟨he.1.1,he.2.1,he.2.2⟩
  exact SimpleGraph.Reachable.mono hm (hx'.symm.trans hy')

end contactComponent

/-- Shortest paths in the spanning graph restricted to a set are
induced in the original graph on their actual vertices. -/
theorem ContactInducedPath.exists_on {G : SimpleGraph W} {U : Set W} {a b : W}
    (ha : a ∈ U) (h : (contactGraphOn G U).Reachable a b) :
    ∃ p : ContactInducedPath G a b, ∀ k ≤ p.length, p.point k ∈ U := by
  obtain ⟨p⟩ := ContactInducedPath.exists_of_reachable h
  have hp : ∀ k ≤ p.length, p.point k ∈ U := by
    intro k hk
    cases k with
    | zero => simpa only [p.start_eq] using ha
    | succ k => exact (p.step k (by omega)).2.2
  let r : ContactInducedPath G a b := {
    length := p.length
    point := p.point
    start_eq := p.start_eq
    end_eq := p.end_eq
    inj := p.inj
    step := fun k hk => (p.step k hk).1
    no_chord := fun i j hij hj he =>
      p.no_chord i j hij hj ⟨he,hp i (by omega),hp j hj⟩
  }
  exact ⟨r,hp⟩

def contactSeparator (G : SimpleGraph W) (a b : W) (s : Finset W) : Prop :=
  a ∉ s ∧ b ∉ s ∧ ¬ (contactGraphOn G {x | x ∉ s}).Reachable a b

open Classical in
structure ContactMinimalSeparator (G : SimpleGraph W) (a b : W) where
  cut : Finset W
  separates : contactSeparator G a b cut
  erase_reachable : ∀ x ∈ cut,
    (contactGraphOn G {y | y ∉ cut.erase x}).Reachable a b

/-- A minimum-cardinality separator exists for any nonadjacent
distinct pair of vertices. Deleting any cut vertex reconnects them. -/
theorem contact_exists_minimalSeparator [Fintype W] (G : SimpleGraph W)
    (a b : W) (hne : a ≠ b) (hna : ¬ G.Adj a b) :
    Nonempty (ContactMinimalSeparator G a b) := by
  classical
  let s := (Finset.univ.erase a).erase b
  have hs : contactSeparator G a b s := by
    have hA : a ∉ s := by simp [s]
    have hB : b ∉ s := by simp [s]
    refine ⟨hA,hB,?_⟩
    intro hr
    have hclosed : ∀ x y, x ∈ ({a} : Set W) →
        (contactGraphOn G {u | u ∉ s}).Adj x y → y ∈ ({a} : Set W) := by
      intro x y hx he
      have hx' : x = a := hx
      subst x
      have hmem : y ∉ s := he.2.2
      have hy : y = a ∨ y = b := by
        by_contra hn
        push_neg at hn
        exact hmem (by simp [s,hn.1,hn.2])
      rcases hy with hy | hy
      · exact hy
      · exact (hna (by simpa only [hy] using he.1)).elim
    have hb : b ∈ ({a} : Set W) :=
      contact_reachable_closed hclosed (by simp) hr
    exact hne.symm hb
  let Q : ℕ → Prop := fun n => ∃ t : Finset W, t.card = n ∧ contactSeparator G a b t
  have hex : ∃ n, Q n := ⟨s.card,s,rfl,hs⟩
  obtain ⟨t,ht,htsep⟩ := Nat.find_spec hex
  refine ⟨⟨t,htsep,?_⟩⟩
  intro x hx
  by_contra hn
  have hsep' : contactSeparator G a b (t.erase x) :=
    ⟨fun h => htsep.1 (Finset.mem_of_mem_erase h),
      fun h => htsep.2.1 (Finset.mem_of_mem_erase h),hn⟩
  have hmin := Nat.find_min' hex
    (show Q (t.erase x).card from ⟨t.erase x,rfl,hsep'⟩)
  have hlt := Finset.card_erase_lt_of_mem hx
  omega

namespace ContactMinimalSeparator
variable {G : SimpleGraph W} {a b : W} (S : ContactMinimalSeparator G a b)

def outside : Set W := {x | x ∉ S.cut}
def left : Set W := contactComponent G S.outside a
def right : Set W := contactComponent G S.outside b

theorem left_root : a ∈ S.left := contactComponent.root S.separates.1
theorem right_root : b ∈ S.right := contactComponent.root S.separates.2.1

theorem sides_disjoint : Disjoint S.left S.right :=
  contactComponent.disjoint S.separates.2.2

theorem sides_no_edge {x y : W} (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.Adj x y := contactComponent.no_cross S.separates.2.2 hx hy

/-- Every minimal separator vertex has a neighbour in each of the
two full components. Otherwise the corresponding component remains
closed even when that cut vertex is restored. -/
theorem neighbour_in_left (x : W) (hx : x ∈ S.cut) :
    ∃ y ∈ S.left, G.Adj x y := by
  classical
  by_contra hn
  have hclosed : ∀ u v, u ∈ S.left →
      (contactGraphOn G {y | y ∉ S.cut.erase x}).Adj u v → v ∈ S.left := by
    intro u v hu he
    by_cases hv : v = x
    · subst v
      exact (hn ⟨u,hu,he.1.symm⟩).elim
    · have hnot : v ∉ S.cut := fun h => he.2.2 (Finset.mem_erase.mpr ⟨hv,h⟩)
      exact contactComponent.closed hu hnot he.1
  have hb := contact_reachable_closed hclosed S.left_root (S.erase_reachable x hx)
  exact S.separates.2.2 hb.2

theorem neighbour_in_right (x : W) (hx : x ∈ S.cut) :
    ∃ y ∈ S.right, G.Adj x y := by
  classical
  by_contra hn
  have hclosed : ∀ u v, u ∈ S.right →
      (contactGraphOn G {y | y ∉ S.cut.erase x}).Adj u v → v ∈ S.right := by
    intro u v hu he
    by_cases hv : v = x
    · subst v
      exact (hn ⟨u,hu,he.1.symm⟩).elim
    · have hnot : v ∉ S.cut := fun h => he.2.2 (Finset.mem_erase.mpr ⟨hv,h⟩)
      exact contactComponent.closed hu hnot he.1
  have ha := contact_reachable_closed hclosed S.right_root
    (S.erase_reachable x hx).symm
  exact S.separates.2.2 ha.2.symm

/-- The separator is a clique. Two nonadjacent cut points would
have an induced path through each full component, and those paths
have separated interiors. -/
theorem cut_clique (hch : ContactChordal G) :
    ∀ x ∈ S.cut, ∀ y ∈ S.cut, x ≠ y → G.Adj x y := by
  classical
  intro x hx y hy hxy
  by_contra hnot
  obtain ⟨xl,hxl,hxl'⟩ := S.neighbour_in_left x hx
  obtain ⟨yl,hyl,hyl'⟩ := S.neighbour_in_left y hy
  obtain ⟨xr,hxr,hxr'⟩ := S.neighbour_in_right x hx
  obtain ⟨yr,hyr,hyr'⟩ := S.neighbour_in_right y hy
  let U : Set W := {z | z ∈ S.left ∨ z = x ∨ z = y}
  let R : Set W := {z | z ∈ S.right ∨ z = y ∨ z = x}
  have xU : x ∈ U := Or.inr (Or.inl rfl)
  have yU : y ∈ U := Or.inr (Or.inr rfl)
  have yR : y ∈ R := Or.inr (Or.inl rfl)
  have xR : x ∈ R := Or.inr (Or.inr rfl)
  have hl : (contactGraphOn G S.left).Reachable xl yl :=
    contactComponent.reachable_inside S.separates.1 hxl hyl
  have hr : (contactGraphOn G S.right).Reachable yr xr :=
    contactComponent.reachable_inside S.separates.2.1 hyr hxr
  have hp : (contactGraphOn G U).Reachable x y :=
    (show (contactGraphOn G U).Adj x xl from ⟨hxl',xU,Or.inl hxl⟩).reachable.trans
      ((SimpleGraph.Reachable.mono (contactGraphOn_mono G (fun _ h => Or.inl h)) hl).trans
        (show (contactGraphOn G U).Adj yl y from ⟨hyl'.symm,Or.inl hyl,yU⟩).reachable)
  have hq : (contactGraphOn G R).Reachable y x :=
    (show (contactGraphOn G R).Adj y yr from ⟨hyr',yR,Or.inl hyr⟩).reachable.trans
      ((SimpleGraph.Reachable.mono (contactGraphOn_mono G (fun _ h => Or.inl h)) hr).trans
        (show (contactGraphOn G R).Adj xr x from ⟨hxr'.symm,Or.inl hxr,xR⟩).reachable)
  obtain ⟨p,hp'⟩ := ContactInducedPath.exists_on xU hp
  obtain ⟨r,hr'⟩ := ContactInducedPath.exists_on yR hq
  have hlen := p.two_le_of_nonadjacent hxy hnot
  have hlen' := r.two_le_of_nonadjacent hxy.symm (fun h => hnot h.symm)
  have hL : ∀ i, 0 < i → i < p.length → p.point i ∈ S.left := by
    intro i hpos hi
    rcases hp' i hi.le with h | h | h
    · exact h
    · exact (p.interior_ne_start hpos hi.le h).elim
    · exact (p.interior_ne_end hi h).elim
  have hR : ∀ i, 0 < i → i < r.length → r.point i ∈ S.right := by
    intro i hpos hi
    rcases hr' i hi.le with h | h | h
    · exact h
    · exact (r.interior_ne_start hpos hi.le h).elim
    · exact (r.interior_ne_end hi h).elim
  exact contact_no_separated_paths hch p r hlen hlen'
    (fun i j hip hi hjp hj he => Set.disjoint_left.mp S.sides_disjoint
      (hL i hip hi) (he.symm ▸ hR j hjp hj))
    (fun i j hip hi hjp hj => S.sides_no_edge (hL i hip hi) (hR j hjp hj))

end ContactMinimalSeparator
end StructuralRamsey.Girth
