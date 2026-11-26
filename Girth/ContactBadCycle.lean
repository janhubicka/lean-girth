import Girth.ContactCoveredSide
import Girth.ContactLowOrder

/-! Common cycle-localization lemmas for preservation, restriction, and
the level-zero forest argument. All use actual simple polygons. -/

namespace StructuralRamsey.Girth

universe v
variable {V P I J : Type v}

theorem contactSucc_value {n : ℕ} (i : Fin n) :
    (cyclicSucc i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  change (i.val + 1) % n = _
  have hi := i.isLt
  by_cases h : i.val + 1 < n
  · simp [h,Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = n := by omega
    simp [h,he]

theorem contactSucc_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    cyclicSucc i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  rw [contactSucc_value] at hv
  split_ifs at hv <;> omega

theorem contactSucc_sq_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    cyclicSucc (cyclicSucc i) ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  have h0 := contactSucc_value i
  have h1 := contactSucc_value (cyclicSucc i)
  have hi := i.isLt
  have hs := (cyclicSucc i).isLt
  split_ifs at h0 h1 <;> omega

theorem contactSucc_surjective {n : ℕ} : Function.Surjective (@cyclicSucc n) := by
  intro i
  have hi := i.isLt
  by_cases h : i.val = 0
  · refine ⟨⟨n-1,by omega⟩,?_⟩
    apply Fin.ext
    rw [contactSucc_value]
    change (if n-1+1 < n then n-1+1 else 0) = i.val
    rw [if_neg (by omega)]
    exact h.symm
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    rw [contactSucc_value]
    change (if i.val-1+1 < n then i.val-1+1 else 0) = i.val
    rw [if_pos (by omega)]
    omega

/-- A predicate closed under cyclic succession holds everywhere if it
holds at position zero. Only ordinary induction on the index is needed. -/
theorem contactCycle_all_of_zero {n : ℕ} (hn : 0 < n)
    (Q : Fin n → Prop) (h0 : Q ⟨0,hn⟩)
    (hs : ∀ i, Q i → Q (cyclicSucc i)) : ∀ i, Q i := by
  have aux : ∀ k : ℕ, ∀ hk : k < n, Q ⟨k,hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      have hlt : k < n := by omega
      have he : cyclicSucc (⟨k,hlt⟩ : Fin n) = ⟨k+1,hk⟩ := by
        apply Fin.ext
        change (k+1) % n = k+1
        exact Nat.mod_eq_of_lt hk
      rw [← he]
      exact hs _ (ih hlt)
  intro i
  exact aux i.val i.isLt

private theorem contact_three_indices_exhaust {n : ℕ} (hn : n = 3)
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    l = i ∨ l = j ∨ l = k := by
  subst n
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

/-- Three pairwise consecutive distinct positions cannot occur in a
cyclic index set of length at least four. -/
private theorem contact_no_three_consecutive {n : ℕ} (hn : 4 ≤ n)
    (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h1 : cyclicSucc i = j ∨ cyclicSucc j = i)
    (h2 : cyclicSucc i = k ∨ cyclicSucc k = i)
    (h3 : cyclicSucc j = k ∨ cyclicSucc k = j) : False := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hne1 : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hne2 : i.val ≠ k.val := fun he => hik (Fin.ext he)
  have hne3 : j.val ≠ k.val := fun he => hjk (Fin.ext he)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    have a := congrArg Fin.val h1 <;>
    have b := congrArg Fin.val h2 <;>
    have c := congrArg Fin.val h3 <;>
    rw [contactSucc_value] at a b c <;>
    split_ifs at a b c <;> omega

namespace ContactPolygon

variable (C : ContactPolygon V P) {K : I → Set (V ⊕ P)}

/-- An uncovered triangle or a chordless longer cycle. -/
def Bad (K : I → Set (V ⊕ P)) : Prop :=
  C.IsCycle K ∧ ¬ C.Covered K ∧ ¬ C.HasChord K

theorem not_chord_of_triangle (h : C.length = 3) : ¬ C.HasChord K := by
  intro hc
  obtain ⟨i,j,hnc,_⟩ := hc
  have aux : ∀ (n : ℕ) (hn : n = 3) (a b : Fin n),
      a ≠ b → cyclicSucc a ≠ b → cyclicSucc b ≠ a → False := by
    intro n hn
    subst n
    intro a b hne h1 h2
    fin_cases a <;> fin_cases b <;> simp_all [cyclicSucc]
  exact aux C.length h i j hnc.1 hnc.2.1 hnc.2.2

theorem consecutive_of_no_chord (h : ¬ C.HasChord K)
    {i j : Fin C.length} (hne : i ≠ j)
    (hadj : contactAdjacent K (C.vertex i) (C.vertex j)) :
    cyclicSucc i = j ∨ cyclicSucc j = i := by
  classical
  by_contra hn
  push_neg at hn
  exact h ⟨i,j,⟨hne,hn.1,hn.2⟩,hadj⟩

/-- Any generating clique meets a bad polygon in at most two vertices.
This works also when the bad polygon is a triangle. -/
theorem bad_no_three (h : C.Bad K) (a : I)
    {i j k : Fin C.length} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : C.vertex i ∈ K a) (hj : C.vertex j ∈ K a) (hk : C.vertex k ∈ K a) :
    False := by
  by_cases htri : C.length = 3
  · apply h.2.1
    refine ⟨a,?_⟩
    intro l
    rcases contact_three_indices_exhaust htri i j k l hij hik hjk with he | he | he
    · simpa only [he] using hi
    · simpa only [he] using hj
    · simpa only [he] using hk
  · have hfour : 4 ≤ C.length := by have := C.hlength; omega
    have adj (s t : Fin C.length) (hne : s ≠ t)
        (hs : C.vertex s ∈ K a) (ht : C.vertex t ∈ K a) :
        contactAdjacent K (C.vertex s) (C.vertex t) :=
      ⟨fun he => hne (C.vertex_injective he),a,hs,ht⟩
    exact contact_no_three_consecutive hfour i j k hij hik hjk
      (C.consecutive_of_no_chord h.2.2 hij (adj i j hij hi hj))
      (C.consecutive_of_no_chord h.2.2 hik (adj i k hik hi hk))
      (C.consecutive_of_no_chord h.2.2 hjk (adj j k hjk hj hk))

/-- In particular the two sides at any point of a bad polygon cannot
both be contained in the same generating clique. -/
theorem bad_no_three_successive (h : C.Bad K) (a : I) (i : Fin C.length)
    (h0 : C.vertex i ∈ K a) (h1 : C.vertex (cyclicSucc i) ∈ K a)
    (h2 : C.vertex (cyclicSucc (cyclicSucc i)) ∈ K a) : False := by
  have hn : 2 ≤ C.length := by have := C.hlength; omega
  exact C.bad_no_three h a (fun he => contactSucc_ne hn i he.symm)
    (fun he => contactSucc_sq_ne C.hlength i he.symm)
    (fun he => contactSucc_ne hn (cyclicSucc i) he.symm) h0 h1 h2

end ContactPolygon

/-- Proving absence of short bad polygons is exactly enough for G4. -/
theorem contactG4_of_no_bad {K : I → Set (V ⊕ P)} {q : ℕ}
    (h : ∀ C : ContactPolygon V P, C.twiceWeight ≤ 2*q → ¬ C.Bad K) :
    ContactG4 K q := by
  classical
  intro C hc hw
  constructor
  · intro htri
    by_contra hnc
    exact h C hw ⟨hc,hnc,C.not_chord_of_triangle htri⟩
  · intro hlen
    by_contra hnd
    have hnc : ¬ C.Covered K := fun hcv => hnd (C.covered_hasChord hlen hcv)
    exact h C hw ⟨hc,hnc,hnd⟩

/-- When all shared chords of the old clique family survive as edges,
any short bad polygon in a smaller graph is contained in one old
generating clique. This is the common localization principle. -/
theorem contact_bad_localizes {K : I → Set (V ⊕ P)} {L : J → Set (V ⊕ P)}
    {q : ℕ} (h4 : ContactG4 K q)
    (hsub : ∀ x y, contactAdjacent L x y → contactAdjacent K x y)
    (hshared : ∀ a b : I, a ≠ b → ∀ x y, x ≠ y →
      x ∈ K a → y ∈ K a → x ∈ K b → y ∈ K b → contactAdjacent L x y)
    (C : ContactPolygon V P) (hw : C.twiceWeight ≤ 2*q) (hb : C.Bad L) :
    C.Covered K := by
  rcases contactSharedChordBound_of_G4 h4 C (fun i => hsub _ _ (hb.1 i)) hw
    with h | hs
  · exact h
  · obtain ⟨i,j,hnc,a,b,hab,hia,hja,hib,hjb⟩ := hs
    exact (hb.2.2 ⟨i,j,hnc,hshared a b hab _ _
      (fun he => hnc.1 (C.vertex_injective he)) hia hja hib hjb⟩).elim

end StructuralRamsey.Girth
