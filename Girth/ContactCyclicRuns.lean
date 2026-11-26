import Girth.ContactBadCycle
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Find

/-! Pure cyclic run enumeration extracted from the old checked proof at
99d26270. No geometric-owner, BigCycle, or replacement dependency is
needed. These results apply directly to owners of the incoming sides
of a contact polygon. -/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- Number of boundaries in a cyclic owner assignment where the
owner of the next occurrence differs. For two or more blocks, this
is the number of maximal cyclic constant-owner segments. -/
noncomputable def contactOwnerChanges (owner : Fin n → Owner) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin n => owner i ≠ owner (cyclicSucc i))).card

/-- Zero changes means the owner is constant along EVERY cyclic
successor edge. This is the one-segment alternative, without a
premature claim that a chosen source is unique. -/
theorem contactOwnerChanges_eq_zero_iff
    (owner : Fin n → Owner) :
    contactOwnerChanges owner = 0 ↔
      ∀ i : Fin n, owner i = owner (cyclicSucc i) := by
  classical
  constructor
  · intro h i
    have hEmpty :
        (Finset.univ.filter
          (fun j : Fin n => owner j ≠ owner (cyclicSucc j))) = ∅ :=
      Finset.card_eq_zero.mp (by
        simpa [contactOwnerChanges] using h)
    by_contra hne
    have hmem : i ∈ Finset.univ.filter
        (fun j : Fin n => owner j ≠ owner (cyclicSucc j)) := by
      simp [hne]
    rw [hEmpty] at hmem
    simpa using hmem
  · intro h
    have hEmpty :
        (Finset.univ.filter
          (fun j : Fin n => owner j ≠ owner (cyclicSucc j))) = ∅ := by
      ext j
      constructor
      · intro hj
        exact False.elim ((Finset.mem_filter.mp hj).2 (h j))
      · intro hj
        simp at hj
    change (Finset.univ.filter
      (fun j : Fin n => owner j ≠ owner (cyclicSucc j))).card = 0
    rw [hEmpty]
    rfl


end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v}

/-- A nonempty finite cyclic owner word has no changes if and only
if all its positions have one common owner. -/
theorem contactOwnerChanges_zero_iff_constant
    {n : ℕ} (hn : 0 < n) (owner : Fin n → Owner) :
    contactOwnerChanges owner = 0 ↔
      ∃ a : Owner, ∀ k : Fin n, owner k = a := by
  constructor
  · intro hZero
    have hSuccessor :=
      (contactOwnerChanges_eq_zero_iff owner).mp hZero
    let zero : Fin n := ⟨0, hn⟩
    have hFromZero : ∀ k : ℕ, ∀ hk : k < n,
        owner ⟨k, hk⟩ = owner zero := by
      intro k
      induction k with
      | zero =>
          intro hk
          rfl
      | succ k ih =>
          intro hSucc
          have hk : k < n := by omega
          have hs : cyclicSucc (⟨k, hk⟩ : Fin n) =
              ⟨k + 1, hSucc⟩ := by
            apply Fin.ext
            change (k + 1) % n = k + 1
            exact Nat.mod_eq_of_lt hSucc
          calc
            owner ⟨k + 1, hSucc⟩ =
                owner (cyclicSucc ⟨k, hk⟩) := by rw [hs]
            _ = owner ⟨k, hk⟩ := (hSuccessor ⟨k, hk⟩).symm
            _ = owner zero := ih hk
    refine ⟨owner zero, ?_⟩
    intro k
    exact hFromZero k.val k.isLt
  · rintro ⟨a, h⟩
    apply (contactOwnerChanges_eq_zero_iff owner).mpr
    intro k
    rw [h k, h (cyclicSucc k)]

/-- Cyclic owner boundaries are concrete positions, with the boundary
after k present exactly when k and its successor have different owners. -/
noncomputable def contactOwnerCutPositions
    {n : ℕ} (owner : Fin n → Owner) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun k => owner k ≠ owner (cyclicSucc k))

theorem mem_contactOwnerCutPositions_iff
    {n : ℕ} (owner : Fin n → Owner) (k : Fin n) :
    k ∈ contactOwnerCutPositions owner ↔
      owner k ≠ owner (cyclicSucc k) := by
  classical
  simp [contactOwnerCutPositions]

/-- The number of actual cyclic cut positions is the numerical
minimization parameter, not merely bounded by that parameter. -/
theorem contactOwnerCutPositions_card
    {n : ℕ} (owner : Fin n → Owner) :
    (contactOwnerCutPositions owner).card =
      contactOwnerChanges owner := rfl

/-- Any nonzero cyclic change count provides an actual boundary
at which the word can be cut and its maximal runs enumerated. -/
theorem exists_contactOwnerCut_of_pos
    {n : ℕ} (owner : Fin n → Owner)
    (hPos : 0 < contactOwnerChanges owner) :
    ∃ k : Fin n, owner k ≠ owner (cyclicSucc k) := by
  by_contra hNot
  have hNoChange : ∀ k : Fin n,
      owner k = owner (cyclicSucc k) := by
    intro k
    by_contra hk
    exact hNot ⟨k, hk⟩
  have hZero := (contactOwnerChanges_eq_zero_iff owner).mpr hNoChange
  omega


end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v

variable {Owner : Type v} {n : ℕ}

/-- Canonical increasing enumeration of ALL cyclic owner cut positions.
The empty cut set gives an empty domain Fin 0. -/
noncomputable def contactOwnerCutIndex (owner : Fin n → Owner) :
    Fin (contactOwnerChanges owner) ↪o Fin n :=
  (contactOwnerCutPositions owner).orderEmbOfFin
    (contactOwnerCutPositions_card owner)

/-- Every finite cut position appears exactly once in this enumeration:
there are no spurious positions and no lost cyclic wrap boundary. -/
theorem contactOwnerCutIndex_image (owner : Fin n → Owner) :
    Finset.image (contactOwnerCutIndex owner)
        (Finset.univ : Finset (Fin (contactOwnerChanges owner))) =
      contactOwnerCutPositions owner := by
  classical
  unfold contactOwnerCutIndex
  exact Finset.image_orderEmbOfFin_univ
    (contactOwnerCutPositions owner)
    (contactOwnerCutPositions_card owner)

/-- Exact membership criterion for the indexed cyclic cut positions. -/
theorem contactOwnerCutIndex_mem_iff (owner : Fin n → Owner) (k : Fin n) :
    k ∈ contactOwnerCutPositions owner ↔
      ∃ j : Fin (contactOwnerChanges owner),
        contactOwnerCutIndex owner j = k := by
  classical
  rw [← contactOwnerCutIndex_image owner]
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

/-- Every enumerated position is a GENUINE owner change. -/
theorem contactOwnerCutIndex_is_change (owner : Fin n → Owner)
    (j : Fin (contactOwnerChanges owner)) :
    owner (contactOwnerCutIndex owner j) ≠
      owner (cyclicSucc (contactOwnerCutIndex owner j)) := by
  apply (mem_contactOwnerCutPositions_iff owner _).mp
  exact (contactOwnerCutIndex_mem_iff owner _).mpr ⟨j, rfl⟩

/-- The indexed cut sequence is strictly increasing in the ambient
Fin order; its successor is not YET identified with the cyclic
next owner-run boundary, including wrap. -/
theorem contactOwnerCutIndex_strictMono (owner : Fin n → Owner) :
    StrictMono (contactOwnerCutIndex owner) :=
  (contactOwnerCutIndex owner).strictMono

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- No actual owner change lies STRICTLY between two consecutive
members of the canonical increasing cut enumeration. -/
theorem contactOwner_no_cut_between_indexed
    (owner : Fin n → Owner)
    (i : Fin (contactOwnerChanges owner))
    (hi : i.val + 1 < contactOwnerChanges owner)
    (t : Fin n)
    (hLower : contactOwnerCutIndex owner i < t)
    (hUpper : t < contactOwnerCutIndex owner
      (⟨i.val + 1, hi⟩ : Fin (contactOwnerChanges owner))) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ contactOwnerCutPositions owner :=
    (mem_contactOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (contactOwnerCutIndex_mem_iff owner t).mp hCut
  have hij : i < j := by
    by_contra hNot
    have hji : j ≤ i := le_of_not_gt hNot
    have hMon : contactOwnerCutIndex owner j ≤
        contactOwnerCutIndex owner i :=
      (contactOwnerCutIndex owner).monotone hji
    rw [hj] at hMon
    exact (not_le_of_gt hLower) hMon
  have hjNext : j < (⟨i.val + 1, hi⟩ :
      Fin (contactOwnerChanges owner)) := by
    by_contra hNot
    have hji : (⟨i.val + 1, hi⟩ :
        Fin (contactOwnerChanges owner)) ≤ j := le_of_not_gt hNot
    have hMon : contactOwnerCutIndex owner
        (⟨i.val + 1, hi⟩ : Fin (contactOwnerChanges owner)) ≤
          contactOwnerCutIndex owner j :=
      (contactOwnerCutIndex owner).monotone hji
    rw [hj] at hMon
    exact (not_le_of_gt hUpper) hMon
  have h1 : i.val < j.val := hij
  have h2 : j.val < i.val + 1 := hjNext
  omega

/-- There is no cut before the first indexed cut (when one exists). -/
theorem contactOwner_no_cut_before_first
    (owner : Fin n → Owner)
    (hk : 0 < contactOwnerChanges owner)
    (t : Fin n)
    (ht : t < contactOwnerCutIndex owner
      (⟨0, hk⟩ : Fin (contactOwnerChanges owner))) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ contactOwnerCutPositions owner :=
    (mem_contactOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (contactOwnerCutIndex_mem_iff owner t).mp hCut
  have hZero : (⟨0, hk⟩ :
      Fin (contactOwnerChanges owner)) ≤ j := by
    change 0 ≤ j.val
    omega
  have hMon := (contactOwnerCutIndex owner).monotone hZero
  rw [hj] at hMon
  exact (not_le_of_gt ht) hMon

/-- There is no cut after the last indexed cut (when one exists).
In particular, the final-to-first cyclic wrap is handled as a
real boundary rather than discarded by linear sorting. -/
theorem contactOwner_no_cut_after_last
    (owner : Fin n → Owner)
    (hk : 0 < contactOwnerChanges owner)
    (t : Fin n)
    (ht : contactOwnerCutIndex owner
      (⟨contactOwnerChanges owner - 1, by omega⟩ :
        Fin (contactOwnerChanges owner)) < t) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ contactOwnerCutPositions owner :=
    (mem_contactOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (contactOwnerCutIndex_mem_iff owner t).mp hCut
  have hjLast : j ≤
      (⟨contactOwnerChanges owner - 1, by omega⟩ :
        Fin (contactOwnerChanges owner)) := by
    change j.val ≤ contactOwnerChanges owner - 1
    have := j.isLt
    omega
  have hMon := (contactOwnerCutIndex owner).monotone hjLast
  rw [hj] at hMon
  exact (not_le_of_gt ht) hMon

/-- Ordinary-interval path induction: if all successor links from
a through b are uncut, then their owners agree. This also records
the exact hypothesis needed for each indexed owner-run interval. -/
theorem contactOwner_constant_on_linear_interval
    (owner : Fin n → Owner) (a b : Fin n)
    (hab : a ≤ b)
    (hNo : ∀ t : Fin n, a ≤ t → t < b →
      owner t = owner (cyclicSucc t)) :
    owner a = owner b := by
  have hAux : ∀ j : ℕ, ∀ hj : j < n,
      a.val ≤ j → j ≤ b.val →
        owner a = owner (⟨j, hj⟩ : Fin n) := by
    intro j
    induction j with
    | zero =>
        intro hj hAj _hJb
        have ha0 : a.val = 0 := by omega
        have hEq : a = (⟨0, hj⟩ : Fin n) := Fin.ext ha0
        exact congrArg owner hEq
    | succ j ih =>
        intro hj hAj hJb
        by_cases hEq : a.val = j + 1
        · have ha : a = (⟨j + 1, hj⟩ : Fin n) := Fin.ext hEq
          exact congrArg owner ha
        · have hjPrev : j < n := by omega
          have hajPrev : a.val ≤ j := by omega
          have hjbPrev : j ≤ b.val := by omega
          have hjBelow : j < b.val := by omega
          have hA : a ≤ (⟨j, hjPrev⟩ : Fin n) := by
            change a.val ≤ j
            exact hajPrev
          have hB : (⟨j, hjPrev⟩ : Fin n) < b := by
            change j < b.val
            exact hjBelow
          have hSucc : cyclicSucc (⟨j, hjPrev⟩ : Fin n) =
              (⟨j + 1, hj⟩ : Fin n) := by
            apply Fin.ext
            change (j + 1) % n = j + 1
            exact Nat.mod_eq_of_lt hj
          calc
            owner a = owner (⟨j, hjPrev⟩ : Fin n) :=
              ih hjPrev hajPrev hjbPrev
            _ = owner (cyclicSucc (⟨j, hjPrev⟩ : Fin n)) :=
              hNo ⟨j, hjPrev⟩ hA hB
            _ = owner (⟨j + 1, hj⟩ : Fin n) := by rw [hSucc]
  simpa using hAux b.val b.isLt (Fin.le_def.mp hab) (le_refl b.val)

/-- The owner is genuinely constant on the indexed maximal run from
just AFTER one cut up to and including the next cut. -/
theorem contactOwner_constant_between_indexed_cuts
    (owner : Fin n → Owner)
    (i : Fin (contactOwnerChanges owner))
    (hi : i.val + 1 < contactOwnerChanges owner)
    (t : Fin n)
    (hLower : contactOwnerCutIndex owner i < t)
    (hUpper : t ≤ contactOwnerCutIndex owner
      (⟨i.val + 1, hi⟩ : Fin (contactOwnerChanges owner))) :
    owner (cyclicSucc (contactOwnerCutIndex owner i)) = owner t := by
  let p := contactOwnerCutIndex owner i
  let q := contactOwnerCutIndex owner
    (⟨i.val + 1, hi⟩ : Fin (contactOwnerChanges owner))
  have hpq : p < q := (contactOwnerCutIndex owner).strictMono (by
    change i.val < i.val + 1
    omega)
  have hp1 : p.val + 1 < n := by
    have hlt : p.val < q.val := hpq
    have hqn := q.isLt
    omega
  have hSuccVal : (cyclicSucc p).val = p.val + 1 := by
    change (p.val + 1) % n = p.val + 1
    exact Nat.mod_eq_of_lt hp1
  have hAB : cyclicSucc p ≤ t := by
    change (cyclicSucc p).val ≤ t.val
    have hpt : p.val < t.val := hLower
    omega
  apply contactOwner_constant_on_linear_interval owner
    (cyclicSucc p) t hAB
  intro u huStart huEnd
  have huL : p < u := by
    have hVal : (cyclicSucc p).val ≤ u.val := huStart
    change p.val < u.val
    omega
  have huR : u < q := by
    have huT : u.val < t.val := huEnd
    have htQ : t.val ≤ q.val := hUpper
    change u.val < q.val
    omega
  exact contactOwner_no_cut_between_indexed owner i hi u huL huR

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- The first indexed actual owner cut. -/
noncomputable def contactOwnerFirstCut
    (owner : Fin n → Owner) (hk : 0 < contactOwnerChanges owner) : Fin n :=
  contactOwnerCutIndex owner ⟨0, hk⟩

/-- The last indexed actual owner cut, in the ordinary Fin order. -/
noncomputable def contactOwnerLastCut
    (owner : Fin n → Owner) (hk : 0 < contactOwnerChanges owner) : Fin n :=
  contactOwnerCutIndex owner
    ⟨contactOwnerChanges owner - 1, by omega⟩

/-- Since there are no cuts before the first indexed cut, ownership
does not change from the physical position 0 to that first cut. -/
theorem contactOwner_zero_eq_first_cut
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < contactOwnerChanges owner) :
    owner (⟨0, hn⟩ : Fin n) =
      owner (contactOwnerFirstCut owner hk) := by
  let zero : Fin n := ⟨0, hn⟩
  let first := contactOwnerFirstCut owner hk
  apply contactOwner_constant_on_linear_interval owner zero first
  · change 0 ≤ first.val
    omega
  · intro t _hlo hhi
    exact contactOwner_no_cut_before_first owner hk t hhi

/-- The tail following the last indexed cut connects through the
actual end-of-word successor to physical position 0. This is the
cyclic wrap case that a linearly indexed list alone cannot prove. -/
theorem contactOwner_last_cut_successor_eq_zero
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < contactOwnerChanges owner) :
    owner (cyclicSucc (contactOwnerLastCut owner hk)) =
      owner (⟨0, hn⟩ : Fin n) := by
  let last := contactOwnerLastCut owner hk
  let zero : Fin n := ⟨0, hn⟩
  by_cases hLast : last.val + 1 = n
  · have hs : cyclicSucc last = zero := by
      apply Fin.ext
      change (last.val + 1) % n = 0
      rw [hLast]
      exact Nat.mod_self n
    rw [hs]
  · have hBelow : last.val + 1 < n := by
      have := last.isLt
      omega
    let start : Fin n := ⟨last.val + 1, hBelow⟩
    let final : Fin n := ⟨n - 1, by omega⟩
    have hSucc : cyclicSucc last = start := by
      apply Fin.ext
      change (last.val + 1) % n = last.val + 1
      exact Nat.mod_eq_of_lt hBelow
    have hBounds : start ≤ final := by
      change last.val + 1 ≤ n - 1
      omega
    have hTail : owner start = owner final :=
      contactOwner_constant_on_linear_interval owner start final hBounds (by
        intro t hStart _hFinal
        have hLastLess : last < t := by
          change last.val < t.val
          have hStartVal : last.val + 1 ≤ t.val := hStart
          omega
        exact contactOwner_no_cut_after_last owner hk t hLastLess)
    have hFinalAbove : last < final := by
      change last.val < n - 1
      omega
    have hFinalNext : owner final = owner (cyclicSucc final) :=
      contactOwner_no_cut_after_last owner hk final hFinalAbove
    have hFinalSucc : cyclicSucc final = zero := by
      apply Fin.ext
      change (n - 1 + 1) % n = 0
      have hN : n - 1 + 1 = n := by omega
      rw [hN]
      exact Nat.mod_self n
    calc
      owner (cyclicSucc last) = owner start := by rw [hSucc]
      _ = owner final := hTail
      _ = owner zero := by rw [hFinalSucc] at hFinalNext; exact hFinalNext

/-- The entire wrap-around run has one owner, from just after the
last linearly indexed cut up through the first cut. -/
theorem contactOwner_wrap_start_eq_first_cut
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < contactOwnerChanges owner) :
    owner (cyclicSucc (contactOwnerLastCut owner hk)) =
      owner (contactOwnerFirstCut owner hk) :=
  (contactOwner_last_cut_successor_eq_zero owner hn hk).trans
    (contactOwner_zero_eq_first_cut owner hn hk)

/-- EVERY occurrence in the cyclic wrap interval shares the owner
at the successor of the last cut. The disjunction describes either
the linear tail or the linear head, including both endpoints. -/
theorem contactOwner_constant_on_wrap_run
    (owner : Fin n → Owner) (hn : 0 < n)
    (hk : 0 < contactOwnerChanges owner)
    (t : Fin n)
    (hIn : contactOwnerLastCut owner hk < t ∨
      t ≤ contactOwnerFirstCut owner hk) :
    owner (cyclicSucc (contactOwnerLastCut owner hk)) = owner t := by
  let last := contactOwnerLastCut owner hk
  let first := contactOwnerFirstCut owner hk
  rcases hIn with hTail | hHead
  · by_cases hLast : last.val + 1 = n
    · have hT := t.isLt
      have hLastT : last.val < t.val := hTail
      omega
    · have hBelow : last.val + 1 < n := by
        have := last.isLt
        omega
      let start : Fin n := ⟨last.val + 1, hBelow⟩
      have hs : cyclicSucc last = start := by
        apply Fin.ext
        change (last.val + 1) % n = last.val + 1
        exact Nat.mod_eq_of_lt hBelow
      have hStart : start ≤ t := by
        change last.val + 1 ≤ t.val
        have hh : last.val < t.val := hTail
        omega
      have hPath : owner start = owner t :=
        contactOwner_constant_on_linear_interval owner start t hStart (by
          intro u hStartU _hUT
          have hLastU : last < u := by
            change last.val < u.val
            have hu : last.val + 1 ≤ u.val := hStartU
            omega
          exact contactOwner_no_cut_after_last owner hk u hLastU)
      rw [hs]
      exact hPath
  · have hToFirst : owner t = owner first :=
      contactOwner_constant_on_linear_interval owner t first hHead (by
        intro u _hStart hBelow
        exact contactOwner_no_cut_before_first owner hk u hBelow)
    exact (contactOwner_wrap_start_eq_first_cut owner hn hk).trans
      hToFirst.symm

/-- In a finite CYCLIC word, exactly one change is impossible.
The proof checks the wrap, not just the linearly ordered prefix. -/
theorem contactOwner_changes_ne_one
    (owner : Fin n → Owner) (hn : 0 < n) :
    contactOwnerChanges owner ≠ 1 := by
  intro hOne
  have hk : 0 < contactOwnerChanges owner := by omega
  have hIdx : (⟨contactOwnerChanges owner - 1, by omega⟩ :
      Fin (contactOwnerChanges owner)) =
      (⟨0, hk⟩ : Fin (contactOwnerChanges owner)) := by
    apply Fin.ext
    change contactOwnerChanges owner - 1 = 0
    omega
  have hCut := contactOwnerCutIndex_is_change owner
    (⟨0, hk⟩ : Fin (contactOwnerChanges owner))
  have hWrap := contactOwner_wrap_start_eq_first_cut owner hn hk
  unfold contactOwnerLastCut contactOwnerFirstCut at hWrap
  rw [hIdx] at hWrap
  exact hCut hWrap.symm

/-- The abstract owner label of the maximal cyclic segment starting
immediately after the corresponding physical cut. -/
noncomputable def contactOwnerRunLabel
    (owner : Fin n → Owner)
    (i : Fin (contactOwnerChanges owner)) : Owner :=
  owner (cyclicSucc (contactOwnerCutIndex owner i))

/-- The owner of one segment equals the owner at the NEXT cyclic cut,
including the indexed last-to-first wrap. -/
theorem contactOwnerRunLabel_eq_next_cut
    (owner : Fin n → Owner)
    (i : Fin (contactOwnerChanges owner)) :
    contactOwnerRunLabel owner i =
      owner (contactOwnerCutIndex owner (cyclicSucc i)) := by
  have hk : 0 < contactOwnerChanges owner := by
    have := i.isLt
    omega
  by_cases hNext : i.val + 1 < contactOwnerChanges owner
  · have hs : cyclicSucc i =
        (⟨i.val + 1, hNext⟩ : Fin (contactOwnerChanges owner)) := by
      apply Fin.ext
      change (i.val + 1) % contactOwnerChanges owner = i.val + 1
      exact Nat.mod_eq_of_lt hNext
    rw [hs]
    unfold contactOwnerRunLabel
    have hlt : contactOwnerCutIndex owner i <
        contactOwnerCutIndex owner
          (⟨i.val + 1, hNext⟩ : Fin (contactOwnerChanges owner)) :=
      (contactOwnerCutIndex owner).strictMono (by
        change i.val < i.val + 1
        omega)
    exact contactOwner_constant_between_indexed_cuts owner i hNext
      (contactOwnerCutIndex owner ⟨i.val + 1, hNext⟩)
      hlt (le_refl _)
  · have hEnd : i.val + 1 = contactOwnerChanges owner := by
      have := i.isLt
      omega
    have hs : cyclicSucc i =
        (⟨0, hk⟩ : Fin (contactOwnerChanges owner)) := by
      apply Fin.ext
      change (i.val + 1) % contactOwnerChanges owner = 0
      rw [hEnd]
      exact Nat.mod_self _
    have hLast : i =
        (⟨contactOwnerChanges owner - 1, by omega⟩ :
          Fin (contactOwnerChanges owner)) := by
      apply Fin.ext
      change i.val = contactOwnerChanges owner - 1
      omega
    have hn : 0 < n := by
      have := (contactOwnerCutIndex owner i).isLt
      omega
    unfold contactOwnerRunLabel
    rw [hs, hLast]
    simpa [contactOwnerFirstCut, contactOwnerLastCut] using
      (contactOwner_wrap_start_eq_first_cut owner hn hk)

/-- Consecutive maximal-segment OWNER LABELS are different, including
the last-to-first pair. This is only an owner-level BigCycle field:
the map from standard owners into witness designated labels still
requires the intended concrete injective copy-index family. -/
theorem contactOwnerRunLabel_adjacent_ne
    (owner : Fin n → Owner)
    (i : Fin (contactOwnerChanges owner)) :
    contactOwnerRunLabel owner i ≠
      contactOwnerRunLabel owner (cyclicSucc i) := by
  rw [contactOwnerRunLabel_eq_next_cut owner i]
  unfold contactOwnerRunLabel
  exact contactOwnerCutIndex_is_change owner (cyclicSucc i)

end StructuralRamsey.Girth
