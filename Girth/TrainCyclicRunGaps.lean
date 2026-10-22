import Girth.TrainCyclicCutIndices
import Mathlib.Tactic

/-!
# Circulation: actual maximal-run gaps of a cyclic owner word

The finite cyclic owner cuts are indexed by the verified increasing
order embedding. There is no OTHER cut strictly between successive
indexed positions. Consequently the owner stays constant from the
successor of one cut up to the next cut, even if the owner type is
infinite. The two ends of the linear indexing are handled separately:
there is no cut before the first or after the last indexed cut.

These are real facts about the ACTUAL owner word, not an assumed
segmentation. The wrap-around owner equality, the physically labelled
reduced witness BigCycle and A1--A3 remain further obligations.
No appendix input.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} {n : ℕ}

/-- No actual owner change lies STRICTLY between two consecutive
members of the canonical increasing cut enumeration. -/
theorem cyclicOwner_no_cut_between_indexed
    (owner : Fin n → Owner)
    (i : Fin (cyclicOwnerChanges owner))
    (hi : i.val + 1 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hLower : cyclicOwnerCutIndex owner i < t)
    (hUpper : t < cyclicOwnerCutIndex owner
      (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner))) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp hCut
  have hij : i < j := by
    by_contra hNot
    have hji : j ≤ i := le_of_not_gt hNot
    have hMon : cyclicOwnerCutIndex owner j ≤
        cyclicOwnerCutIndex owner i :=
      (cyclicOwnerCutIndex owner).monotone hji
    rw [hj] at hMon
    exact (not_le_of_gt hLower) hMon
  have hjNext : j < (⟨i.val + 1, hi⟩ :
      Fin (cyclicOwnerChanges owner)) := by
    by_contra hNot
    have hji : (⟨i.val + 1, hi⟩ :
        Fin (cyclicOwnerChanges owner)) ≤ j := le_of_not_gt hNot
    have hMon : cyclicOwnerCutIndex owner
        (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner)) ≤
          cyclicOwnerCutIndex owner j :=
      (cyclicOwnerCutIndex owner).monotone hji
    rw [hj] at hMon
    exact (not_le_of_gt hUpper) hMon
  have h1 : i.val < j.val := hij
  have h2 : j.val < i.val + 1 := hjNext
  omega

/-- There is no cut before the first indexed cut (when one exists). -/
theorem cyclicOwner_no_cut_before_first
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (ht : t < cyclicOwnerCutIndex owner
      (⟨0, hk⟩ : Fin (cyclicOwnerChanges owner))) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp hCut
  have hZero : (⟨0, hk⟩ :
      Fin (cyclicOwnerChanges owner)) ≤ j := by
    change 0 ≤ j.val
    omega
  have hMon := (cyclicOwnerCutIndex owner).monotone hZero
  rw [hj] at hMon
  exact (not_le_of_gt ht) hMon

/-- There is no cut after the last indexed cut (when one exists).
In particular, the final-to-first cyclic wrap is handled as a
real boundary rather than discarded by linear sorting. -/
theorem cyclicOwner_no_cut_after_last
    (owner : Fin n → Owner)
    (hk : 0 < cyclicOwnerChanges owner)
    (t : Fin n)
    (ht : cyclicOwnerCutIndex owner
      (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
        Fin (cyclicOwnerChanges owner)) < t) :
    owner t = owner (cyclicSucc t) := by
  by_contra hNe
  have hCut : t ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner t).mpr hNe
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp hCut
  have hjLast : j ≤
      (⟨cyclicOwnerChanges owner - 1, by omega⟩ :
        Fin (cyclicOwnerChanges owner)) := by
    change j.val ≤ cyclicOwnerChanges owner - 1
    have := j.isLt
    omega
  have hMon := (cyclicOwnerCutIndex owner).monotone hjLast
  rw [hj] at hMon
  exact (not_le_of_gt ht) hMon

/-- Ordinary-interval path induction: if all successor links from
a through b are uncut, then their owners agree. This also records
the exact hypothesis needed for each indexed owner-run interval. -/
theorem cyclicOwner_constant_on_linear_interval
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
theorem cyclicOwner_constant_between_indexed_cuts
    (owner : Fin n → Owner)
    (i : Fin (cyclicOwnerChanges owner))
    (hi : i.val + 1 < cyclicOwnerChanges owner)
    (t : Fin n)
    (hLower : cyclicOwnerCutIndex owner i < t)
    (hUpper : t ≤ cyclicOwnerCutIndex owner
      (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner))) :
    owner (cyclicSucc (cyclicOwnerCutIndex owner i)) = owner t := by
  let p := cyclicOwnerCutIndex owner i
  let q := cyclicOwnerCutIndex owner
    (⟨i.val + 1, hi⟩ : Fin (cyclicOwnerChanges owner))
  have hpq : p < q := (cyclicOwnerCutIndex owner).strictMono (by
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
  apply cyclicOwner_constant_on_linear_interval owner
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
  exact cyclicOwner_no_cut_between_indexed owner i hi u huL huR

end StructuralRamsey.Girth
