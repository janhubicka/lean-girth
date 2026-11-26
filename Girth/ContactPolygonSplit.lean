import Girth.ContactCycles
import Girth.ContactCyclicRestriction

/-! Actual chord splitting for the two-sort contact polygons.
The two children are increasing enumerations of the closed interval
[i,j] and its complementary cyclic arc, retaining both endpoints.
The old (cycle-word independent) restriction inequality bounds their
weights, and source adjacency reflection lifts every child chord. -/

namespace StructuralRamsey.Girth

universe v
variable {V P J : Type v} {K : J → Set (V ⊕ P)}

private theorem cyclicSucc_value {n : ℕ} (i : Fin n) :
    (cyclicSucc i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  change (i.val + 1) % n = _
  have hi := i.isLt
  by_cases h : i.val + 1 < n
  · simp [h, Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = n := by omega
    simp [h, he]

private def intervalEmbedding {n : ℕ} (i j : Fin n) (h : i.val ≤ j.val) :
    Fin (j.val - i.val + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun k => ⟨i.val + k.val, by have := k.isLt; have := j.isLt; omega⟩)
    (by
      intro a b hab
      change a.val < b.val at hab
      change i.val + a.val < i.val + b.val
      omega)

private theorem intervalEmbedding_value {n : ℕ} (i j : Fin n)
    (h : i.val ≤ j.val) (k : Fin (j.val - i.val + 1)) :
    (intervalEmbedding i j h k).val = i.val + k.val := rfl

private def complementEmbedding {n : ℕ} (i j : Fin n) (h : i.val < j.val) :
    Fin (n - j.val + i.val + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun k => ⟨if k.val ≤ i.val then k.val else k.val + (j.val - i.val - 1),
      by have := k.isLt; have := i.isLt; have := j.isLt; split <;> omega⟩)
    (by
      intro a b hab
      change a.val < b.val at hab
      change (if a.val ≤ i.val then a.val else a.val + (j.val - i.val - 1)) <
        (if b.val ≤ i.val then b.val else b.val + (j.val - i.val - 1))
      split_ifs <;> omega)

private theorem complementEmbedding_value {n : ℕ} (i j : Fin n)
    (h : i.val < j.val) (k : Fin (n - j.val + i.val + 1)) :
    (complementEmbedding i j h k).val =
      if k.val ≤ i.val then k.val else k.val + (j.val - i.val - 1) := rfl

private theorem interval_mem {n : ℕ} {i j k : Fin n}
    (h : i.val ≤ j.val) (hlo : i.val ≤ k.val) (hhi : k.val ≤ j.val) :
    k ∈ Set.range (intervalEmbedding i j h) := by
  refine ⟨⟨k.val - i.val, by omega⟩, ?_⟩
  apply Fin.ext
  rw [intervalEmbedding_value]
  omega

private theorem complement_mem_low {n : ℕ} {i j k : Fin n}
    (h : i.val < j.val) (hk : k.val ≤ i.val) :
    k ∈ Set.range (complementEmbedding i j h) := by
  have hj := j.isLt
  refine ⟨⟨k.val, by omega⟩, ?_⟩
  apply Fin.ext
  rw [complementEmbedding_value, if_pos hk]

private theorem complement_mem_high {n : ℕ} {i j k : Fin n}
    (h : i.val < j.val) (hk : j.val ≤ k.val) :
    k ∈ Set.range (complementEmbedding i j h) := by
  have hk' := k.isLt
  let a := k.val - (j.val - i.val - 1)
  have ha : i.val < a := by dsimp [a]; omega
  refine ⟨⟨a, by dsimp [a]; omega⟩, ?_⟩
  apply Fin.ext
  rw [complementEmbedding_value, if_neg (by exact Nat.not_le_of_lt ha)]
  dsimp [a]
  omega

/-- Every side of the restricted polygon is an original side, except
the last-to-first side, which is the specified chord in reverse. -/
private theorem interval_side {n : ℕ} {i j : Fin n} (h : i.val < j.val)
    (k : Fin (j.val - i.val + 1)) :
    intervalEmbedding i j h.le (cyclicSucc k) =
        cyclicSucc (intervalEmbedding i j h.le k) ∨
      (intervalEmbedding i j h.le k = j ∧
        intervalEmbedding i j h.le (cyclicSucc k) = i) := by
  have hk := k.isLt
  have hj := j.isLt
  by_cases hnext : k.val + 1 < j.val - i.val + 1
  · left
    apply Fin.ext
    simp only [intervalEmbedding_value, cyclicSucc_value]
    split_ifs <;> omega
  · right
    constructor
    · apply Fin.ext
      rw [intervalEmbedding_value]
      omega
    · apply Fin.ext
      simp only [intervalEmbedding_value, cyclicSucc_value]
      rw [if_neg hnext]
      omega

/-- Every side of the complementary polygon is an original side, except
the increasing side from i to j, which is the specified chord. -/
private theorem complement_side {n : ℕ} {i j : Fin n} (h : i.val < j.val)
    (k : Fin (n - j.val + i.val + 1)) :
    complementEmbedding i j h (cyclicSucc k) =
        cyclicSucc (complementEmbedding i j h k) ∨
      (complementEmbedding i j h k = i ∧
        complementEmbedding i j h (cyclicSucc k) = j) := by
  have hk := k.isLt
  have hj := j.isLt
  have hi := i.isLt
  by_cases he : k.val = i.val
  · right
    constructor
    · apply Fin.ext
      simp only [complementEmbedding_value]
      split_ifs <;> omega
    · apply Fin.ext
      simp only [complementEmbedding_value, cyclicSucc_value]
      split_ifs <;> omega
  · left
    apply Fin.ext
    simp only [complementEmbedding_value, cyclicSucc_value]
    split_ifs <;> omega

namespace ContactPolygon

/-- Restrict to an increasing enumeration of a set of polygon vertices. -/
def restrict (C : ContactPolygon V P) {m : ℕ} (hm : 3 ≤ m)
    (f : Fin m ↪o Fin C.length) : ContactPolygon V P where
  length := m
  hlength := hm
  vertex := C.vertex ∘ f
  vertex_injective := C.vertex_injective.comp f.injective

theorem restrict_weight_le (C : ContactPolygon V P) {m : ℕ} (hm : 3 ≤ m)
    (f : Fin m ↪o Fin C.length) :
    (C.restrict hm f).twiceWeight ≤ C.twiceWeight := by
  have hn : 2 ≤ C.length := by have := C.hlength; omega
  exact ContactCyclicRestriction.twiceWeight_restrict_le hn f
    (fun i => contactKind (C.vertex i))

theorem restrict_nonc (C : ContactPolygon V P) {m : ℕ} (hm : 3 ≤ m)
    (f : Fin m ↪o Fin C.length) (i j : Fin m)
    (h : (C.restrict hm f).Nonconsecutive i j) :
    C.Nonconsecutive (f i) (f j) := by
  refine ⟨fun he => h.1 (f.injective he), ?_, ?_⟩
  · intro he
    exact h.2.1 (ContactCyclicRestriction.successor_of_source_successor f i j he.symm).symm
  · intro he
    exact h.2.2 (ContactCyclicRestriction.successor_of_source_successor f j i he.symm).symm

private theorem split_of_ordered_chord (C : ContactPolygon V P) (hc : C.IsCycle K)
    (i j : Fin C.length) (hij : i.val < j.val) (hnc : C.Nonconsecutive i j)
    (hadj : contactAdjacent K (C.vertex i) (C.vertex j)) :
    Nonempty (C.Split K) := by
  have hi := i.isLt
  have hj := j.isLt
  have hgap : i.val + 1 < j.val := by
    by_contra hn
    have he : i.val + 1 = j.val := by omega
    apply hnc.2.1
    apply Fin.ext
    rw [cyclicSucc_value, if_pos (by omega)]
    exact he
  have hwrap : j.val + 1 < C.length + i.val := by
    by_contra hn
    have hzero : i.val = 0 := by omega
    have hlast : j.val + 1 = C.length := by omega
    apply hnc.2.2
    apply Fin.ext
    rw [cyclicSucc_value, if_neg (by omega)]
    omega
  have hL : 3 ≤ j.val - i.val + 1 := by omega
  have hR : 3 ≤ C.length - j.val + i.val + 1 := by omega
  let f := intervalEmbedding i j hij.le
  let g := complementEmbedding i j hij
  have hs : contactAdjacent K (C.vertex j) (C.vertex i) := by
    obtain ⟨hne,a,ha,hb⟩ := hadj
    exact ⟨hne.symm,a,hb,ha⟩
  refine ⟨{
    left := C.restrict hL f
    right := C.restrict hR g
    leftMap := f
    rightMap := g
    left_vertex := fun _ => rfl
    right_vertex := fun _ => rfl
    left_cycle := ?_
    right_cycle := ?_
    left_weight := C.restrict_weight_le hL f
    right_weight := C.restrict_weight_le hR g
    left_smaller := by change j.val - i.val + 1 < C.length; omega
    right_smaller := by change C.length - j.val + i.val + 1 < C.length; omega
    left_nonc := fun a b h => C.restrict_nonc hL f a b h
    right_nonc := fun a b h => C.restrict_nonc hR g a b h
    cover := ?_
    side_cover := ?_
    chord := ?_
  }⟩
  · intro k
    change contactAdjacent K (C.vertex (f k)) (C.vertex (f (cyclicSucc k)))
    rcases interval_side hij k with h | ⟨h1,h2⟩
    · change f (cyclicSucc k) = cyclicSucc (f k) at h
      rw [h]
      exact hc (f k)
    · change f k = j at h1
      change f (cyclicSucc k) = i at h2
      rw [h1,h2]
      exact hs
  · intro k
    change contactAdjacent K (C.vertex (g k)) (C.vertex (g (cyclicSucc k)))
    rcases complement_side hij k with h | ⟨h1,h2⟩
    · change g (cyclicSucc k) = cyclicSucc (g k) at h
      rw [h]
      exact hc (g k)
    · change g k = i at h1
      change g (cyclicSucc k) = j at h2
      rw [h1,h2]
      exact hadj
  · intro k
    by_cases hl : k.val ≤ i.val
    · exact Or.inr (complement_mem_low hij hl)
    by_cases hr : j.val ≤ k.val
    · exact Or.inr (complement_mem_high hij hr)
    · exact Or.inl (interval_mem hij.le (by omega) (by omega))
  · intro k
    have hk := k.isLt
    have hside :
        (k ∈ Set.range f ∧ cyclicSucc k ∈ Set.range f) ∨
          (k ∈ Set.range g ∧ cyclicSucc k ∈ Set.range g) := by
      by_cases hki : k.val < i.val
      · right
        refine ⟨complement_mem_low hij (by omega), complement_mem_low hij ?_⟩
        rw [cyclicSucc_value, if_pos (by omega)]
        omega
      by_cases hkj : k.val < j.val
      · left
        refine ⟨interval_mem hij.le (by omega) (by omega), interval_mem hij.le ?_ ?_⟩
        · rw [cyclicSucc_value, if_pos (by omega)]
          omega
        · rw [cyclicSucc_value, if_pos (by omega)]
          omega
      · right
        refine ⟨complement_mem_high hij (by omega), ?_⟩
        by_cases hnext : k.val + 1 < C.length
        · apply complement_mem_high hij
          rw [cyclicSucc_value, if_pos hnext]
          omega
        · apply complement_mem_low hij
          rw [cyclicSucc_value, if_neg hnext]
          omega
    rcases hside with ⟨⟨a,ha⟩,⟨b,hb⟩⟩ | ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    · left
      have hab : b = cyclicSucc a :=
        ContactCyclicRestriction.successor_of_source_successor f a b (by rw [ha,hb])
      exact ⟨a,ha,by rw [← hab,hb]⟩
    · right
      have hab : b = cyclicSucc a :=
        ContactCyclicRestriction.successor_of_source_successor g a b (by rw [ha,hb])
      exact ⟨a,ha,by rw [← hab,hb]⟩
  · exact ⟨i,j,hnc,interval_mem hij.le (le_refl _) hij.le,
      interval_mem hij.le hij.le (le_refl _),complement_mem_low hij (le_refl _),
      complement_mem_high hij (le_refl _)⟩

/-- Every actual chord yields the complete split record; no weight,
intersection, or cyclic interval hypothesis remains external. -/
theorem split_of_chord (C : ContactPolygon V P)
    (hc : C.IsCycle K) (hd : C.HasChord K) :
    Nonempty (C.Split K) := by
  obtain ⟨i,j,hnc,hadj⟩ := hd
  by_cases h : i.val < j.val
  · exact C.split_of_ordered_chord hc i j h hnc hadj
  · have hne : i.val ≠ j.val := fun he => hnc.1 (Fin.ext he)
    have hj : j.val < i.val := by omega
    have hrev : C.Nonconsecutive j i := ⟨hnc.1.symm,hnc.2.2,hnc.2.1⟩
    have ha : contactAdjacent K (C.vertex j) (C.vertex i) := by
      obtain ⟨hne',a,ha,hb⟩ := hadj
      exact ⟨hne'.symm,a,hb,ha⟩
    exact C.split_of_ordered_chord hc j i hj hrev ha

end ContactPolygon

/-- The full shared-chord alternative, for the actual two-sort weights. -/
theorem contactSharedChordBound_of_G4 {q : ℕ} (h : ContactG4 K q) :
    ContactSharedChordBound K q :=
  contactSharedChordBound_of_G4_of_splits h
    (fun C hc hd => C.split_of_chord hc hd)

theorem contactSharedChordBound_iff_G4 {q : ℕ} :
    ContactSharedChordBound K q ↔ ContactG4 K q :=
  ⟨contactG4_of_sharedChordBound, contactSharedChordBound_of_G4⟩

end StructuralRamsey.Girth
