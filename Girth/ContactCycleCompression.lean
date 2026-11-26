import Girth.ContactCyclicRuns

/-! Compress a cyclic walk of wagon labels to a genuine labelled
Berge cycle. Unlike the historical incidence-acyclicity argument,
this directly retains the number of actual changes, which gives
the factor-two refinement gain. -/

namespace StructuralRamsey.Girth
universe v
variable {V P : Type v}

/-- A cyclic word of adjacent distinct labels with distinct
connectors gives a labelled Berge cycle of at most its length.
If labels repeat, use a shortest interval between equal labels.
The final connector of that interval closes the new cycle. -/
theorem contact_cycle_of_closed_incidence {n : ℕ}
    (K : P → Set V) (hn : 2 ≤ n)
    (lab : Fin n → P) (z : Fin n → V) (hz : Function.Injective z)
    (hne : ∀ i, lab i ≠ lab (cyclicSucc i))
    (hl : ∀ i, z i ∈ K (lab i))
    (hr : ∀ i, z i ∈ K (lab (cyclicSucc i))) :
    ∃ C : LabelledBergeCycle K, C.length ≤ n := by
  classical
  by_cases hi : Function.Injective lab
  · exact ⟨⟨n,hn,lab,z,hi,hz,hl,hr⟩,le_rfl⟩
  have hrep : ∃ k : ℕ, ∃ i j : Fin n, i.val < j.val ∧
      j.val-i.val = k ∧ lab i = lab j := by
    have hex : ∃ i j, lab i = lab j ∧ i ≠ j := by
      by_contra h
      apply hi
      intro i j he
      by_contra hij
      exact h ⟨i,j,he,hij⟩
    obtain ⟨i,j,he,hij⟩ := hex
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hlt : i.val < j.val
    · exact ⟨j.val-i.val,i,j,hlt,rfl,he⟩
    · exact ⟨i.val-j.val,j,i,by omega,rfl,he.symm⟩
  let k := Nat.find hrep
  obtain ⟨a,b,hab,hk,heq⟩ := Nat.find_spec hrep
  have hkpos : 0 < k := by omega
  have hktwo : 2 ≤ k := by
    by_contra h
    have hs : cyclicSucc a = b := by
      apply Fin.ext
      have hb := b.isLt
      rw [contactSucc_value,if_pos (by omega)]
      omega
    apply hne a
    rw [hs]
    exact heq
  have hkn : k ≤ n := by have := b.isLt; omega
  let idx : Fin k → Fin n := fun t =>
    ⟨a.val+t.val,by have ht := t.isLt; have hb := b.isLt; omega⟩
  have hidx : Function.Injective idx := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change a.val+i.val = a.val+j.val at hv
    omega
  have hlabel : Function.Injective (lab ∘ idx) := by
    intro i j h
    apply Fin.ext
    by_contra hn'
    have hi := i.isLt
    have hj := j.isLt
    have aux (u w : Fin k) (hlt : u.val < w.val)
        (he : lab (idx u) = lab (idx w)) : False := by
      have hu := u.isLt
      have hw := w.isLt
      have hlt' : (idx u).val < (idx w).val := by
        change a.val+u.val < a.val+w.val
        omega
      have hmin := Nat.find_min' hrep
        (show ∃ x y : Fin n, x.val < y.val ∧
          y.val-x.val = (idx w).val-(idx u).val ∧ lab x = lab y
          from ⟨idx u,idx w,hlt',rfl,he⟩)
      change k ≤ a.val+w.val-(a.val+u.val) at hmin
      omega
    by_cases hlt : i.val < j.val
    · exact aux i j hlt h
    · exact aux j i (by omega) h.symm
  have hnext : ∀ t : Fin k, lab (cyclicSucc (idx t)) = lab (idx (cyclicSucc t)) := by
    intro t
    have ht := t.isLt
    have hb := b.isLt
    have hi : (idx t).val+1 < n := by
      change a.val+t.val+1 < n
      omega
    by_cases hlt : t.val+1 < k
    · congr 1
      apply Fin.ext
      rw [contactSucc_value,if_pos hi]
      change a.val+t.val+1 = a.val+(cyclicSucc t).val
      rw [contactSucc_value,if_pos hlt]
      omega
    · have hfirst : idx (cyclicSucc t) = a := by
        apply Fin.ext
        change a.val+(cyclicSucc t).val = a.val
        rw [contactSucc_value,if_neg hlt]
        omega
      have hlast : cyclicSucc (idx t) = b := by
        apply Fin.ext
        rw [contactSucc_value,if_pos hi]
        change a.val+t.val+1 = b.val
        omega
      rw [hfirst,hlast]
      exact heq.symm
  let C : LabelledBergeCycle K := {
    length := k
    hlength := hktwo
    label := lab ∘ idx
    vertex := z ∘ idx
    label_injective := hlabel
    vertex_injective := hz.comp hidx
    left_mem := fun i => hl (idx i)
    right_mem := by
      intro i
      change z (idx i) ∈ K (lab (idx (cyclicSucc i)))
      rw [← hnext i]
      exact hr (idx i)
  }
  exact ⟨C,hkn⟩

/-- A nonconstant owner word on the edges of a genuine Berge
cycle yields a labelled Berge cycle among the owner carriers,
with length at most the number of owner changes. -/
theorem LabelledBergeCycle.contact_compress_owners {E : Type v}
    {edge : E → Set V} (C : LabelledBergeCycle edge)
    (owner : Fin C.length → P) (K : P → Set V)
    (hContained : ∀ i, edge (C.label i) ⊆ K (owner i))
    (hnon : ¬ ∃ p, ∀ i, owner i = p) :
    ∃ B : LabelledBergeCycle K, B.length ≤ contactOwnerChanges owner := by
  classical
  have hn : 0 < C.length := by have := C.hlength; omega
  have h0 : contactOwnerChanges owner ≠ 0 :=
    fun h => hnon ((contactOwnerChanges_zero_iff_constant hn owner).mp h)
  have h1 := contactOwner_changes_ne_one owner hn
  have h2 : 2 ≤ contactOwnerChanges owner := by omega
  let cut := contactOwnerCutIndex owner
  let lab := owner ∘ cut
  let z := C.vertex ∘ cut
  have hnext (i : Fin (contactOwnerChanges owner)) :
      lab (cyclicSucc i) = owner (cyclicSucc (cut i)) :=
    (contactOwnerRunLabel_eq_next_cut owner i).symm
  apply contact_cycle_of_closed_incidence K h2 lab z
    (C.vertex_injective.comp cut.injective)
  · intro i
    change owner (cut i) ≠ lab (cyclicSucc i)
    rw [hnext]
    exact contactOwnerCutIndex_is_change owner i
  · intro i
    exact hContained (cut i) (C.left_mem (cut i))
  · intro i
    change C.vertex (cut i) ∈ K (lab (cyclicSucc i))
    rw [hnext]
    exact hContained (cyclicSucc (cut i)) (C.right_mem (cut i))

/-- For singleton-part intersections, two consecutive owner
changes are impossible: their connectors would be distinct
vertices of the intervening transversal edge in one part. -/
theorem LabelledBergeCycle.contact_no_adjacent_changes {E Part : Type v}
    {edge : E → Set V} (C : LabelledBergeCycle edge)
    (owner : Fin C.length → P) (K : P → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hPart : ∀ e, Set.InjOn part (edge e))
    (hContained : ∀ i, edge (C.label i) ⊆ K (owner i))
    (hInter : ∀ p r, p ≠ r → K p ∩ K r ⊆ part ⁻¹' allowed) :
    ∀ i, i ∈ contactOwnerCutPositions owner →
      cyclicSucc i ∉ contactOwnerCutPositions owner := by
  intro i hi hj
  have hne := (mem_contactOwnerCutPositions_iff owner i).mp hi
  have hne' := (mem_contactOwnerCutPositions_iff owner (cyclicSucc i)).mp hj
  have hx := hInter _ _ hne
    ⟨hContained i (C.left_mem i),hContained _ (C.right_mem i)⟩
  have hy := hInter _ _ hne'
    ⟨hContained _ (C.left_mem (cyclicSucc i)),hContained _ (C.right_mem (cyclicSucc i))⟩
  have he := hPart (C.label (cyclicSucc i)) (C.right_mem i)
    (C.left_mem (cyclicSucc i)) (hAllowed hx hy)
  exact contactSucc_ne C.hlength i (C.vertex_injective he).symm

/-- The change positions and their successor positions are
disjoint sets of the same cardinality. Hence each change
accounts for at least two actual edges. -/
theorem contact_twice_changes_le {n : ℕ} (owner : Fin n → P)
    (hsep : ∀ i, i ∈ contactOwnerCutPositions owner →
      cyclicSucc i ∉ contactOwnerCutPositions owner) :
    2 * contactOwnerChanges owner ≤ n := by
  classical
  let cut := contactOwnerCutPositions owner
  let next := cut.image cyclicSucc
  have hd : Disjoint cut next := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj'
    exact hsep i hi hj
  have hc : cut.card = contactOwnerChanges owner :=
    contactOwnerCutPositions_card owner
  have hn : next.card = cut.card :=
    Finset.card_image_of_injective _ ContactCyclicRestriction.contactCyclicSucc_injective
  have hb : (cut ∪ next).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (cut ∪ next))
  rw [Finset.card_union_of_disjoint hd,hc,hn,hc] at hb
  omega

/-- Quantitative single-cut localization, in its sharper form:
a genuine cycle changing owners at all has at least g+1 changes. -/
theorem LabelledBergeCycle.contact_changes_gt {E : Type v}
    {edge : E → Set V} (C : LabelledBergeCycle edge)
    (owner : Fin C.length → P) (K : P → Set V)
    (hContained : ∀ i, edge (C.label i) ⊆ K (owner i))
    {g : ℕ} (hg : LabelledGirthGT K g)
    (hnon : ¬ ∃ p, ∀ i, owner i = p) :
    g < contactOwnerChanges owner := by
  by_contra h
  obtain ⟨B,hB⟩ := C.contact_compress_owners owner K hContained hnon
  exact hg ⟨B,by omega⟩

end StructuralRamsey.Girth
