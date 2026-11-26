import Girth.ContactRunSegments

/-! Canonical doubled-slot indexing of a subdivided cyclic word.
All even slots are retained. Odd slots are retained exactly on the
selected sides. The sorted retained slots give a single actual finite
cyclic enumeration; the wrap is proved explicitly. -/

namespace StructuralRamsey.Girth

def contactEvenSlot {n : ℕ} (i : Fin n) : Fin (2*n) :=
  ⟨2*i.val,by have := i.isLt; omega⟩

def contactOddSlot {n : ℕ} (i : Fin n) : Fin (2*n) :=
  ⟨2*i.val+1,by have := i.isLt; omega⟩

theorem contactEvenSlot_injective {n : ℕ} : Function.Injective (@contactEvenSlot n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2*i.val = 2*j.val at hv
  omega

theorem contactOddSlot_injective {n : ℕ} : Function.Injective (@contactOddSlot n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2*i.val+1 = 2*j.val+1 at hv
  omega

theorem contactEvenSlot_ne_odd {n : ℕ} (i j : Fin n) :
    contactEvenSlot i ≠ contactOddSlot j := by
  intro h
  have hv := congrArg Fin.val h
  change 2*i.val = 2*j.val+1 at hv
  omega

theorem contactEvenSlot_succ {n : ℕ} (i : Fin n) :
    cyclicSucc (contactEvenSlot i) = contactOddSlot i := by
  apply Fin.ext
  change (2*i.val+1) % (2*n) = 2*i.val+1
  exact Nat.mod_eq_of_lt (by have := i.isLt; omega)

theorem contactOddSlot_succ {n : ℕ} (i : Fin n) :
    cyclicSucc (contactOddSlot i) = contactEvenSlot (cyclicSucc i) := by
  apply Fin.ext
  change (2*i.val+1+1) % (2*n) = 2*((cyclicSucc i).val)
  rw [contactSucc_value]
  by_cases h : i.val+1 < n
  · rw [if_pos h,Nat.mod_eq_of_lt (by omega)]
    omega
  · have he : i.val+1 = n := by have := i.isLt; omega
    have hsum : 2*i.val+1+1 = 2*n := by omega
    rw [if_neg h,hsum,Nat.mod_self]
    rfl

universe v
variable {P : Type v} {n : ℕ}

namespace ContactSlots

variable (ins : Fin n → Option P)

noncomputable def selected : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ins i ≠ none)

theorem mem_selected (i : Fin n) : i ∈ selected ins ↔ ins i ≠ none := by
  classical
  simp [selected]

noncomputable def kept : Finset (Fin (2*n)) := by
  classical
  exact Finset.univ.image contactEvenSlot ∪ (selected ins).image contactOddSlot

noncomputable def enum : Fin (kept ins).card ↪o Fin (2*n) :=
  (kept ins).orderEmbOfFin rfl

theorem enum_image : Finset.univ.image (enum ins) = kept ins := by
  classical
  exact Finset.image_orderEmbOfFin_univ (kept ins) rfl

theorem enum_mem (k : Fin (kept ins).card) : enum ins k ∈ kept ins := by
  classical
  rw [← enum_image ins]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩

theorem exists_index {t : Fin (2*n)} (ht : t ∈ kept ins) :
    ∃ k, enum ins k = t := by
  classical
  rw [← enum_image ins] at ht
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp ht
  exact ⟨k,hk⟩

theorem even_kept (i : Fin n) : contactEvenSlot i ∈ kept ins := by
  classical
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem odd_kept_iff (i : Fin n) :
    contactOddSlot i ∈ kept ins ↔ ins i ≠ none := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with he | ho
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp he
      exact (contactEvenSlot_ne_odd j i hj).elim
    · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ho
      have hji := contactOddSlot_injective he
      subst j
      exact (mem_selected ins i).mp hj
  · intro h
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨i,(mem_selected ins i).mpr h,rfl⟩))

noncomputable def original (i : Fin n) : Fin (kept ins).card :=
  Classical.choose (exists_index ins (even_kept ins i))

theorem original_slot (i : Fin n) :
    enum ins (original ins i) = contactEvenSlot i :=
  Classical.choose_spec (exists_index ins (even_kept ins i))

theorem original_injective : Function.Injective (original ins) := by
  intro i j he
  apply contactEvenSlot_injective
  rw [← original_slot ins i,← original_slot ins j,he]

noncomputable def inserted (i : Fin n) (h : ins i ≠ none) : Fin (kept ins).card :=
  Classical.choose (exists_index ins ((odd_kept_iff ins i).mpr h))

theorem inserted_slot (i : Fin n) (h : ins i ≠ none) :
    enum ins (inserted ins i h) = contactOddSlot i :=
  Classical.choose_spec (exists_index ins ((odd_kept_iff ins i).mpr h))

theorem original_ne_inserted (i j : Fin n) (h : ins j ≠ none) :
    original ins i ≠ inserted ins j h := by
  intro he
  exact contactEvenSlot_ne_odd i j (by rw [← original_slot ins i,he,inserted_slot])

theorem inserted_injective {i j : Fin n} (hi : ins i ≠ none) (hj : ins j ≠ none)
    (he : inserted ins i hi = inserted ins j hj) : i = j := by
  apply contactOddSlot_injective
  rw [← inserted_slot ins i hi,← inserted_slot ins j hj,he]

theorem count_ge : n ≤ (kept ins).card := by
  simpa using Fintype.card_le_of_injective (original ins) (original_injective ins)

/-- Every index of the expansion is either an original point or the
unique odd slot of a selected side. -/
theorem cover (k : Fin (kept ins).card) :
    (∃ i, original ins i = k) ∨
      (∃ i (h : ins i ≠ none), inserted ins i h = k) := by
  classical
  have hk := enum_mem ins k
  rcases Finset.mem_union.mp hk with he | ho
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨i,(enum ins).injective ((original_slot ins i).trans hi)⟩
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ho
    have hn := (mem_selected ins i).mp hi
    exact Or.inr ⟨i,hn,(enum ins).injective ((inserted_slot ins i hn).trans he)⟩

theorem split_first (i : Fin n) (h : ins i ≠ none) :
    cyclicSucc (original ins i) = inserted ins i h := by
  symm
  apply ContactCyclicRestriction.successor_of_source_successor (enum ins)
  rw [original_slot,inserted_slot,contactEvenSlot_succ]

theorem split_second (i : Fin n) (h : ins i ≠ none) :
    cyclicSucc (inserted ins i h) = original ins (cyclicSucc i) := by
  symm
  apply ContactCyclicRestriction.successor_of_source_successor (enum ins)
  rw [original_slot,inserted_slot,contactOddSlot_succ]

/-- If no odd slot is retained, the successor of the original point
is the next original point, including at the cyclic wrap. -/
theorem direct_next (i : Fin n) (h : ins i = none) :
    cyclicSucc (original ins i) = original ins (cyclicSucc i) := by
  classical
  have hnot : contactOddSlot i ∉ kept ins :=
    fun hm => (odd_kept_iff ins i).mp hm h
  have hi := i.isLt
  have hs := contactSucc_value i
  symm
  by_cases hnext : i.val+1 < n
  · rw [if_pos hnext] at hs
    apply ContactCyclicRestriction.successor_of_increasing_gap (enum ins)
    · rw [original_slot,original_slot]
      change 2*i.val < 2*(cyclicSucc i).val
      omega
    · intro k hl hu
      rw [original_slot] at hl hu
      change 2*i.val < (enum ins k).val at hl
      change (enum ins k).val < 2*(cyclicSucc i).val at hu
      have he : enum ins k = contactOddSlot i := by
        apply Fin.ext
        change (enum ins k).val = 2*i.val+1
        omega
      exact hnot (he ▸ enum_mem ins k)
  · rw [if_neg hnext] at hs
    have hlast : i.val+1 = n := by omega
    apply ContactCyclicRestriction.successor_of_wrapping_gap (enum ins)
    · intro k hk
      rw [original_slot] at hk
      change 2*i.val < (enum ins k).val at hk
      have hb := (enum ins k).isLt
      have he : enum ins k = contactOddSlot i := by
        apply Fin.ext
        change (enum ins k).val = 2*i.val+1
        omega
      exact hnot (he ▸ enum_mem ins k)
    · intro k hk
      rw [original_slot] at hk
      change (enum ins k).val < 2*(cyclicSucc i).val at hk
      omega

end ContactSlots
end StructuralRamsey.Girth
