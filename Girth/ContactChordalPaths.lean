import Girth.ContactBadCycle
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Short induced paths and the separated-path obstruction to
chordality. This is a generic graph-theoretic ingredient of the
converse join-tree theorem, independent of train or Ramsey data. -/

namespace StructuralRamsey.Girth
universe v
variable {W : Type v}

/-- The ordinary chordal-graph property, using the same finite
cyclic indices as the weighted polygon library. -/
def ContactChordal (G : SimpleGraph W) : Prop :=
  ∀ (n : ℕ) (z : Fin n → W), 4 ≤ n → Function.Injective z →
    (∀ i, G.Adj (z i) (z (cyclicSucc i))) →
    ∃ i j, i ≠ j ∧ cyclicSucc i ≠ j ∧ cyclicSucc j ≠ i ∧ G.Adj (z i) (z j)

theorem contactChordal_induce {G : SimpleGraph W} (h : ContactChordal G)
    (s : Set W) : ContactChordal (G.induce s) := by
  intro n z hn hi ha
  obtain ⟨i,j,hij,h1,h2,h3⟩ :=
    h n (Subtype.val ∘ z) hn (Subtype.val_injective.comp hi) ha
  exact ⟨i,j,hij,h1,h2,h3⟩

/-- A shortest path, recorded only on the integer interval from zero
through its length. Values outside that interval are irrelevant. -/
structure ContactInducedPath (G : SimpleGraph W) (a b : W) where
  length : ℕ
  point : ℕ → W
  start_eq : point 0 = a
  end_eq : point length = b
  inj : ∀ i j, i ≤ length → j ≤ length → point i = point j → i = j
  step : ∀ i, i < length → G.Adj (point i) (point (i+1))
  no_chord : ∀ i j, i < j → j ≤ length →
    G.Adj (point i) (point j) → j = i+1

namespace ContactInducedPath

/-- A shortest walk has no chord: replacing the interval between
two chord endpoints by one edge would shorten the walk. -/
theorem exists_of_reachable {G : SimpleGraph W} {a b : W}
    (h : G.Reachable a b) : Nonempty (ContactInducedPath G a b) := by
  classical
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist
  have hpath := p.isPath_of_length_eq_dist hp
  refine ⟨{
    length := p.length
    point := p.getVert
    start_eq := p.getVert_zero
    end_eq := p.getVert_of_length_le (le_refl _)
    inj := ?_
    step := fun i hi => p.adj_getVert_succ hi
    no_chord := ?_
  }⟩
  · intro i j hi hj he
    exact hpath.getVert_injOn hi hj he
  · intro i j hij hj hadj
    let w := ((p.take i).append hadj.toWalk).append (p.drop j)
    have hw := G.dist_le w
    have hlen : w.length = i + 1 + (p.length-j) := by
      simp [w,SimpleGraph.Walk.length_append,SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length,Nat.min_eq_left (show i ≤ p.length by omega)]
    omega

/-- Shortest paths in an induced subgraph are also induced paths
in the ambient graph. All their points remain in the prescribed set. -/
theorem exists_in_set {G : SimpleGraph W} {s : Set W} {a b : W}
    (ha : a ∈ s) (hb : b ∈ s)
    (h : (G.induce s).Reachable ⟨a,ha⟩ ⟨b,hb⟩) :
    ∃ p : ContactInducedPath G a b, ∀ k ≤ p.length, p.point k ∈ s := by
  obtain ⟨p⟩ := exists_of_reachable h
  let q : ContactInducedPath G a b := {
    length := p.length
    point := fun k => (p.point k).val
    start_eq := congrArg Subtype.val p.start_eq
    end_eq := congrArg Subtype.val p.end_eq
    inj := fun i j hi hj he => p.inj i j hi hj (Subtype.ext he)
    step := p.step
    no_chord := fun i j hij hj he => p.no_chord i j hij hj he
  }
  exact ⟨q,fun k _ => (p.point k).property⟩

theorem two_le_of_nonadjacent {G : SimpleGraph W} {a b : W}
    (p : ContactInducedPath G a b) (hne : a ≠ b) (hna : ¬ G.Adj a b) :
    2 ≤ p.length := by
  by_contra h
  by_cases hz : p.length = 0
  · have he := p.end_eq
    rw [hz,p.start_eq] at he
    exact hne he
  · have h1 : p.length = 1 := by omega
    have he := p.step 0 (by omega)
    have hlast : p.point 1 = b := by rw [← h1]; exact p.end_eq
    exact hna (by simpa only [p.start_eq,zero_add,hlast] using he)

/-- No interior point of an induced path is one of its endpoints. -/
theorem interior_ne_start {G : SimpleGraph W} {a b : W}
    (p : ContactInducedPath G a b) {i : ℕ} (hi : 0 < i) (hil : i ≤ p.length) :
    p.point i ≠ a := by
  intro he
  have h := p.inj i 0 hil (Nat.zero_le _) (he.trans p.start_eq.symm)
  omega

theorem interior_ne_end {G : SimpleGraph W} {a b : W}
    (p : ContactInducedPath G a b) {i : ℕ} (hi : i < p.length) :
    p.point i ≠ b := by
  intro he
  have h := p.inj i p.length hi.le le_rfl (he.trans p.end_eq.symm)
  omega

end ContactInducedPath

/-- The union of two oppositely oriented induced paths with the same
endpoints and separated interiors gives a chordless polygon. -/
theorem contact_no_separated_paths {G : SimpleGraph W}
    (hch : ContactChordal G) {a b : W}
    (p : ContactInducedPath G a b) (r : ContactInducedPath G b a)
    (hp : 2 ≤ p.length) (hr : 2 ≤ r.length)
    (hdisj : ∀ i j, 0 < i → i < p.length → 0 < j → j < r.length →
      p.point i ≠ r.point j)
    (hcross : ∀ i j, 0 < i → i < p.length → 0 < j → j < r.length →
      ¬ G.Adj (p.point i) (r.point j)) : False := by
  let n := p.length+r.length
  let z : Fin n → W := fun i =>
    if i.val < p.length then p.point i.val else r.point (i.val-p.length)
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hzP (i : Fin n) (hi : i.val < p.length) : z i = p.point i.val := by
    simp only [z,if_pos hi]
  have hzR (i : Fin n) (hi : ¬ i.val < p.length) : z i = r.point (i.val-p.length) := by
    simp only [z,if_neg hi]
  have hzInj : Function.Injective z := by
    intro i j he
    have hi := i.isLt
    have hj := j.isLt
    change i.val < p.length+r.length at hi
    change j.val < p.length+r.length at hj
    apply Fin.ext
    by_cases hiP : i.val < p.length
    · by_cases hjP : j.val < p.length
      · exact p.inj _ _ hiP.le hjP.le ((hzP i hiP).symm.trans (he.trans (hzP j hjP)))
      · have he' := (hzP i hiP).symm.trans (he.trans (hzR j hjP))
        have hjR : j.val-p.length < r.length := by omega
        by_cases hi0 : i.val = 0
        · rw [hi0,p.start_eq] at he'
          exact (r.interior_ne_end hjR he'.symm).elim
        · by_cases hj0 : j.val-p.length = 0
          · rw [hj0,r.start_eq] at he'
            exact (p.interior_ne_end hiP he').elim
          · exact (hdisj _ _ (by omega) hiP (by omega) hjR he').elim
    · by_cases hjP : j.val < p.length
      · have he' := (hzP j hjP).symm.trans (he.symm.trans (hzR i hiP))
        have hiR : i.val-p.length < r.length := by omega
        by_cases hj0 : j.val = 0
        · rw [hj0,p.start_eq] at he'
          exact (r.interior_ne_end hiR he'.symm).elim
        · by_cases hi0 : i.val-p.length = 0
          · rw [hi0,r.start_eq] at he'
            exact (p.interior_ne_end hjP he').elim
          · exact (hdisj _ _ (by omega) hjP (by omega) hiR he').elim
      · have hiR : i.val-p.length ≤ r.length := by omega
        have hjR : j.val-p.length ≤ r.length := by omega
        have he' := r.inj _ _ hiR hjR ((hzR i hiP).symm.trans (he.trans (hzR j hjP)))
        omega
  have hzStep : ∀ i : Fin n, G.Adj (z i) (z (cyclicSucc i)) := by
    intro i
    have hi := i.isLt
    change i.val < p.length+r.length at hi
    have hs := contactSucc_value i
    change (cyclicSucc i).val = (if i.val+1 < p.length+r.length then i.val+1 else 0) at hs
    by_cases hlast : i.val+1 < p.length+r.length
    · rw [if_pos hlast] at hs
      by_cases hiP : i.val < p.length
      · rw [hzP i hiP]
        by_cases hnext : i.val+1 < p.length
        · rw [hzP _ (by omega),hs]
          exact p.step _ hiP
        · have he : i.val+1 = p.length := by omega
          rw [hzR _ (by omega),hs,he,Nat.sub_self,r.start_eq,← p.end_eq,← he]
          exact p.step _ hiP
      · rw [hzR i hiP,hzR _ (by omega),hs]
        have he : i.val+1-p.length = (i.val-p.length)+1 := by omega
        rw [he]
        exact r.step _ (by omega)
    · rw [if_neg hlast] at hs
      have hiR : ¬ i.val < p.length := by omega
      have he : (i.val-p.length)+1 = r.length := by omega
      rw [hzR i hiR,hzP _ (by omega),hs,p.start_eq,← r.end_eq,← he]
      exact r.step _ (by omega)
  /- It suffices to consider increasing index pairs. A same-arc edge
  is a path side, and a cross-arc edge either touches a common endpoint
  or is forbidden by the separated interiors hypothesis. -/
  have ordered_adj : ∀ i j : Fin n, i.val < j.val → G.Adj (z i) (z j) →
      cyclicSucc i = j ∨ cyclicSucc j = i := by
    intro i j hij ha
    have hi := i.isLt
    have hj := j.isLt
    change i.val < p.length+r.length at hi
    change j.val < p.length+r.length at hj
    have consecutive : j.val = i.val+1 → cyclicSucc i = j ∨ cyclicSucc j = i := by
      intro he
      left
      apply Fin.ext
      rw [contactSucc_value,if_pos (by omega)]
      exact he.symm
    by_cases hiP : i.val < p.length
    · by_cases hjP : j.val < p.length
      · rw [hzP i hiP,hzP j hjP] at ha
        exact consecutive (p.no_chord _ _ hij hjP.le ha)
      · rw [hzP i hiP,hzR j hjP] at ha
        have hjR : j.val-p.length < r.length := by omega
        by_cases hi0 : i.val = 0
        · rw [hi0,p.start_eq,← r.end_eq] at ha
          have hlen := r.no_chord _ _ hjR le_rfl ha.symm
          right
          apply Fin.ext
          rw [contactSucc_value,if_neg (by omega)]
          exact hi0.symm
        · by_cases hj0 : j.val-p.length = 0
          · rw [hj0,r.start_eq,← p.end_eq] at ha
            have hlen := p.no_chord _ _ hiP le_rfl ha
            exact consecutive (by omega)
          · exact (hcross _ _ (by omega) hiP (by omega) hjR ha).elim
    · have hjP : ¬ j.val < p.length := by omega
      rw [hzR i hiP,hzR j hjP] at ha
      have he := r.no_chord (i.val-p.length) (j.val-p.length)
        (by omega) (by omega) ha
      exact consecutive (by omega)
  obtain ⟨i,j,hij,hn1,hn2,ha⟩ := hch n z hn hzInj hzStep
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  by_cases hlt : i.val < j.val
  · rcases ordered_adj i j hlt ha with h | h
    · exact hn1 h
    · exact hn2 h
  · rcases ordered_adj j i (by omega) ha.symm with h | h
    · exact hn2 h
    · exact hn1 h

end StructuralRamsey.Girth
