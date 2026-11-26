import Girth.ContactCyclicRuns

/-! The closed cyclic arcs between successive actual owner changes.
We use owners of incoming sides: the two sides at position k have
owners owner k and owner (cyclicSucc k). Therefore the increasing
enumeration of the change positions is already the required order
embedding on boundary vertices. -/

namespace StructuralRamsey.Girth
universe v
variable {Z O : Type v}

/-- The closed forward arc in the ordinary Fin order, including wrap. -/
def contactClosedArc {n : ℕ} (a b t : Fin n) : Prop :=
  if a.val < b.val then a.val ≤ t.val ∧ t.val ≤ b.val
  else a.val ≤ t.val ∨ t.val ≤ b.val

theorem contactClosedArc_left {n : ℕ} (a b : Fin n) :
    contactClosedArc a b a := by
  unfold contactClosedArc
  split_ifs <;> omega

theorem contactClosedArc_right {n : ℕ} (a b : Fin n) :
    contactClosedArc a b b := by
  unfold contactClosedArc
  split_ifs <;> omega

/-- A forward arc along an actual polygon side has no interior. -/
theorem contactClosedArc_short {n : ℕ} (hn : 2 ≤ n) (a t : Fin n)
    (ht : contactClosedArc a (cyclicSucc a) t) :
    t = a ∨ t = cyclicSucc a := by
  have ha := a.isLt
  have hb := (cyclicSucc a).isLt
  have hs := contactSucc_value a
  unfold contactClosedArc at ht
  by_cases h : a.val + 1 < n
  · rw [if_pos h] at hs
    rw [if_pos (by omega)] at ht
    by_cases he : t.val = a.val
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext (by omega))
  · rw [if_neg h] at hs
    rw [if_neg (by omega)] at ht
    rcases ht with ht | ht
    · exact Or.inl (Fin.ext (by have := t.isLt; omega))
    · exact Or.inr (Fin.ext (by omega))

/-- A segment presentation of a cyclic polygon, with an actual
increasing enumeration of its boundaries and actual closed arcs.
The owner labels at consecutive segments differ. -/
structure ContactRunSegments {n : ℕ} (z : Fin n → Z)
    (K : O → Set Z) where
  count : ℕ
  two : 2 ≤ count
  boundary : Fin count ↪o Fin n
  owner : Fin count → O
  adjacent_ne : ∀ i, owner i ≠ owner (cyclicSucc i)
  arc_mem : ∀ i t, contactClosedArc (boundary i) (boundary (cyclicSucc i)) t →
    z t ∈ K (owner i)
  arc_cover : ∀ t, ∃ i, contactClosedArc (boundary i) (boundary (cyclicSucc i)) t

namespace ContactRunSegments

variable {n : ℕ} {z : Fin n → Z} {K : O → Set Z}
    (S : ContactRunSegments z K)

theorem left_mem (i : Fin S.count) : z (S.boundary i) ∈ K (S.owner i) :=
  S.arc_mem i _ (contactClosedArc_left _ _)

theorem right_mem (i : Fin S.count) :
    z (S.boundary (cyclicSucc i)) ∈ K (S.owner i) :=
  S.arc_mem i _ (contactClosedArc_right _ _)

/-- For at least three boundaries, two consecutive boundaries in the
full polygon must be consecutive in the forward direction. -/
theorem forward_of_consecutive (h3 : 3 ≤ S.count) (i : Fin S.count)
    (h : cyclicSucc (S.boundary i) = S.boundary (cyclicSucc i) ∨
      cyclicSucc (S.boundary (cyclicSucc i)) = S.boundary i) :
    cyclicSucc (S.boundary i) = S.boundary (cyclicSucc i) := by
  rcases h with h | h
  · exact h
  · have he := ContactCyclicRestriction.successor_of_source_successor
      S.boundary (cyclicSucc i) i h.symm
    exact (contactSucc_sq_ne h3 i he.symm).elim

end ContactRunSegments

/-- The canonical run construction covers all cyclic positions,
including the final-to-initial arc. This is a statement about the
actual cut enumeration, not a choice of an assumed decomposition. -/
theorem contactOwner_arcs_cover {n : ℕ} (owner : Fin n → O)
    (hk : 0 < contactOwnerChanges owner) (t : Fin n) :
    ∃ i : Fin (contactOwnerChanges owner),
      contactClosedArc (contactOwnerCutIndex owner i)
        (contactOwnerCutIndex owner (cyclicSucc i)) t := by
  classical
  let m := contactOwnerChanges owner
  let f := contactOwnerCutIndex owner
  let first : Fin m := ⟨0,hk⟩
  let last : Fin m := ⟨m-1,by omega⟩
  have hwrap : cyclicSucc last = first := by
    apply Fin.ext
    change (m-1+1) % m = 0
    rw [show m-1+1 = m by omega,Nat.mod_self]
  have hf : (f first).val ≤ (f last).val :=
    f.monotone (by change 0 ≤ m-1; omega)
  by_cases hout : (f last).val ≤ t.val ∨ t.val ≤ (f first).val
  · refine ⟨last,?_⟩
    change contactClosedArc (f last) (f (cyclicSucc last)) t
    rw [hwrap]
    unfold contactClosedArc
    rw [if_neg (by omega)]
    exact hout
  · have ht0 : (f first).val < t.val := by omega
    have ht1 : t.val < (f last).val := by omega
    let Q : ℕ → Prop := fun k => ∃ h : k < m, t.val ≤ (f ⟨k,h⟩).val
    have hex : ∃ k, Q k := ⟨last.val,last.isLt,by omega⟩
    let k := Nat.find hex
    obtain ⟨hkm,hkbound⟩ : Q k := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      have hfin : (⟨k,hkm⟩ : Fin m) = first := by
        apply Fin.ext
        exact he
      rw [hfin] at hkbound
      omega
    let i : Fin m := ⟨k-1,by omega⟩
    have hnext : cyclicSucc i = (⟨k,hkm⟩ : Fin m) := by
      apply Fin.ext
      change (k-1+1) % m = k
      rw [show k-1+1 = k by omega,Nat.mod_eq_of_lt hkm]
    have hlo : (f i).val < t.val := by
      by_contra h
      have hmin : k ≤ k-1 := Nat.find_min' hex
        (show Q (k-1) from ⟨i.isLt,by change t.val ≤ (f i).val; omega⟩)
      omega
    have hfi : (f i).val < (f (⟨k,hkm⟩ : Fin m)).val :=
      f.strictMono (by change k-1 < k; omega)
    refine ⟨i,?_⟩
    change contactClosedArc (f i) (f (cyclicSucc i)) t
    rw [hnext]
    unfold contactClosedArc
    rw [if_pos hfi]
    exact ⟨hlo.le,hkbound⟩

/-- Every point of a canonical arc lies in the corresponding
constituent. At its first boundary use the outgoing side, and at
all other positions use constancy of the incoming-side owner. -/
theorem contactOwner_arc_mem {n : ℕ} (hn : 0 < n)
    (owner : Fin n → O) (z : Fin n → Z) (K : O → Set Z)
    (hmem : ∀ k, z k ∈ K (owner k) ∧ z k ∈ K (owner (cyclicSucc k)))
    (i : Fin (contactOwnerChanges owner)) (t : Fin n)
    (ht : contactClosedArc (contactOwnerCutIndex owner i)
      (contactOwnerCutIndex owner (cyclicSucc i)) t) :
    z t ∈ K (contactOwnerRunLabel owner i) := by
  classical
  let m := contactOwnerChanges owner
  let f := contactOwnerCutIndex owner
  have hm : 0 < m := by have := i.isLt; omega
  by_cases he : t = f i
  · subst t
    exact (hmem (f i)).2
  have hconst : contactOwnerRunLabel owner i = owner t := by
    by_cases hi : i.val + 1 < m
    · have hs : cyclicSucc i = (⟨i.val+1,hi⟩ : Fin m) := by
        apply Fin.ext
        change (i.val+1) % m = i.val+1
        exact Nat.mod_eq_of_lt hi
      have hlt : (f i).val < (f (⟨i.val+1,hi⟩ : Fin m)).val :=
        f.strictMono (by change i.val < i.val+1; omega)
      change contactClosedArc (f i) (f (cyclicSucc i)) t at ht
      rw [hs] at ht
      unfold contactClosedArc at ht
      rw [if_pos hlt] at ht
      have hne : t.val ≠ (f i).val := fun h => he (Fin.ext h)
      exact contactOwner_constant_between_indexed_cuts owner i hi t
        (by change (f i).val < t.val; omega) ht.2
    · have hl : i = (⟨m-1,by omega⟩ : Fin m) := by
        apply Fin.ext
        have := i.isLt
        omega
      have hs : cyclicSucc i = (⟨0,hm⟩ : Fin m) := by
        apply Fin.ext
        change (i.val+1) % m = 0
        rw [show i.val+1 = m by have := i.isLt; omega,Nat.mod_self]
      have hle : (f (⟨0,hm⟩ : Fin m)).val ≤ (f i).val :=
        f.monotone (by change 0 ≤ i.val; omega)
      change contactClosedArc (f i) (f (cyclicSucc i)) t at ht
      rw [hs] at ht
      unfold contactClosedArc at ht
      rw [if_neg (by omega)] at ht
      have hne : t.val ≠ (f i).val := fun h => he (Fin.ext h)
      have hArc : contactOwnerLastCut owner hm < t ∨
          t ≤ contactOwnerFirstCut owner hm := by
        change f (⟨m-1,by omega⟩ : Fin m) < t ∨
          t ≤ f (⟨0,hm⟩ : Fin m)
        rw [← hl]
        rcases ht with h | h
        · left
          change (f i).val < t.val
          omega
        · exact Or.inr h
      unfold contactOwnerRunLabel
      rw [hl]
      exact contactOwner_constant_on_wrap_run owner hn hm t hArc
  rw [hconst]
  exact (hmem t).1

/-- Construct the segment presentation from a nonconstant actual
incoming-side owner assignment. -/
noncomputable def contactSegments_of_owners {n : ℕ} (hn : 0 < n)
    (owner : Fin n → O) (z : Fin n → Z) (K : O → Set Z)
    (hmem : ∀ k, z k ∈ K (owner k) ∧ z k ∈ K (owner (cyclicSucc k)))
    (hnon : ¬ ∃ a, ∀ k, owner k = a) :
    ContactRunSegments z K := by
  have h0 : contactOwnerChanges owner ≠ 0 := fun h =>
    hnon ((contactOwnerChanges_zero_iff_constant hn owner).mp h)
  have h1 := contactOwner_changes_ne_one owner hn
  have htwo : 2 ≤ contactOwnerChanges owner := by omega
  exact {
    count := contactOwnerChanges owner
    two := htwo
    boundary := contactOwnerCutIndex owner
    owner := contactOwnerRunLabel owner
    adjacent_ne := contactOwnerRunLabel_adjacent_ne owner
    arc_mem := contactOwner_arc_mem hn owner z K hmem
    arc_cover := contactOwner_arcs_cover owner (by omega)
  }

end StructuralRamsey.Girth
