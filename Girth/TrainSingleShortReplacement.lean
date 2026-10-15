import Girth.TrainShortReplacementGlobal
import Girth.TrainBigCycleOrderBudget

/-!
# Circulation: one globally legal short replacement

Short replacements do not change connectors. Replacing one occurrence at a
time therefore needs only the genuinely local legality checks: the new label
must differ from its two cyclic neighbours and must be incident with the two
unchanged boundary connectors.

The resulting word is a literal BigCycle. Its order, A2 and A3 are inherited
from the original cycle. At order one, retaining any other designated
occurrence discharges A1. The final inductive relation packages a finite
sequence of such steps away from one retained supreme occurrence.
-/

namespace StructuralRamsey.Girth

/-- Cyclic predecessor and successor are inverse on a genuine cycle. -/
theorem trainCyclicPred_cyclicSucc_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    trainCyclicPred (cyclicSucc i) = i := by
  apply Fin.ext
  simp only [trainCyclicPred, cyclicSucc, Fin.val_mk]
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    have heq : i.val + 1 + n - 1 = i.val + n := by omega
    rw [heq]
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · have hs : i.val + 1 = n := by omega
    rw [hs, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

/-- The converse cyclic inverse follows from the left inverse on the finite
index type. -/
theorem cyclicSucc_trainCyclicPred_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    cyclicSucc (trainCyclicPred i) = i := by
  have hLeft : Function.LeftInverse
      (trainCyclicPred : Fin n → Fin n) cyclicSucc :=
    fun j => trainCyclicPred_cyclicSucc_of_two_le hn j
  have hInj : Function.Injective (cyclicSucc : Fin n → Fin n) :=
    hLeft.injective
  have hSurj : Function.Surjective (cyclicSucc : Fin n → Fin n) :=
    Finite.surjective_of_injective hInj
  obtain ⟨j, hj⟩ := hSurj i
  have hp : trainCyclicPred i = j := by
    rw [← hj]
    exact trainCyclicPred_cyclicSucc_of_two_le hn j
  rw [hp, hj]

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The label function obtained by changing one cyclic occurrence. -/
def BigCycle.replaceLabelAt
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E) :
    Fin n → I ⊕ E :=
  fun i => if i = k then a else C.label i

/-- Two neighbour inequalities and the two boundary incidences are enough to
turn a one-occurrence short replacement into a genuine BigCycle. -/
def BigCycle.replaceOne
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E)
    (hPrev : C.label (trainCyclicPred k) ≠ a)
    (hNext : a ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident a (C.connector k))
    (hRight : D.Incident a (C.connector (trainCyclicPred k))) :
    D.BigCycle n := by
  classical
  apply C.relabelSameConnectors D (C.replaceLabelAt D k a)
  · intro i
    by_cases hik : i = k
    · subst i
      have hsk : cyclicSucc k ≠ k := by
        intro h
        exact C.adjacent_ne k (congrArg C.label h.symm)
      simpa [BigCycle.replaceLabelAt, hsk] using hNext
    · by_cases hsk : cyclicSucc i = k
      · have hip : i = trainCyclicPred k := by
          have h := congrArg trainCyclicPred hsk
          rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at h
          exact h
        have hpk : trainCyclicPred k ≠ k := by
          intro hp
          have hs := congrArg cyclicSucc hp
          rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k] at hs
          exact (C.adjacent_ne k) (congrArg C.label hs)
        have hsp : cyclicSucc (trainCyclicPred k) = k :=
          cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k
        simpa [BigCycle.replaceLabelAt, hik, hsk, hip, hpk, hsp] using hPrev
      · simpa [BigCycle.replaceLabelAt, hik, hsk] using C.adjacent_ne i
  · intro i
    by_cases hik : i = k
    · subst i
      simpa [BigCycle.replaceLabelAt] using hLeft
    · simpa [BigCycle.replaceLabelAt, hik] using C.left_incident i
  · intro i
    by_cases hsk : cyclicSucc i = k
    · have hip : i = trainCyclicPred k := by
        have h := congrArg trainCyclicPred hsk
        rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at h
        exact h
      have hsp : cyclicSucc (trainCyclicPred k) = k :=
        cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two k
      simpa [BigCycle.replaceLabelAt, hsk, hip, hsp] using hRight
    · simpa [BigCycle.replaceLabelAt, hsk] using C.right_incident i

/-- One legal short replacement preserves the numerical order exactly. -/
theorem BigCycle.replaceOne_twiceOrder
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E)
    (hPrev : C.label (trainCyclicPred k) ≠ a)
    (hNext : a ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident a (C.connector k))
    (hRight : D.Incident a (C.connector (trainCyclicPred k))) :
    (C.replaceOne D k a hPrev hNext hLeft hRight).twiceOrder =
      C.twiceOrder :=
  C.relabelSameConnectors_twiceOrder D
    (C.replaceLabelAt D k a)
    (C.replaceOne D k a hPrev hNext hLeft hRight).adjacent_ne
    (C.replaceOne D k a hPrev hNext hLeft hRight).left_incident
    (C.replaceOne D k a hPrev hNext hLeft hRight).right_incident

/-- A big cycle with at least three occurrences cannot have order one. -/
theorem BigCycle.twiceOrder_ne_two_of_three_le_length
    {n : ℕ} (C : D.BigCycle n) (hn : 3 ≤ n) :
    C.twiceOrder ≠ 2 := by
  intro h
  have hTwo := C.length_eq_two_of_order_one D h
  omega

/-- Above order one a legal one-occurrence short replacement preserves full
acceptability without any designation bookkeeping. -/
theorem BigCycle.replaceOne_acceptable_of_order_ne_one
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E)
    (hPrev : C.label (trainCyclicPred k) ≠ a)
    (hNext : a ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident a (C.connector k))
    (hRight : D.Incident a (C.connector (trainCyclicPred k)))
    (hOrder : C.twiceOrder ≠ 2)
    (hAccept : C.Acceptable) :
    (C.replaceOne D k a hPrev hNext hLeft hRight).Acceptable := by
  exact C.relabelSameConnectors_acceptable_of_order_ne_one D
    (C.replaceLabelAt D k a)
    (C.replaceOne D k a hPrev hNext hLeft hRight).adjacent_ne
    (C.replaceOne D k a hPrev hNext hLeft hRight).left_incident
    (C.replaceOne D k a hPrev hNext hLeft hRight).right_incident
    hOrder hAccept

/-- If another designated occurrence is retained, one legal short replacement
preserves acceptability even at order one. -/
theorem BigCycle.replaceOne_acceptable_of_other_designated
    {n : ℕ} (C : D.BigCycle n) (k r : Fin n) (a : I ⊕ E)
    (hrk : r ≠ k) (hr : D.designated (C.label r))
    (hPrev : C.label (trainCyclicPred k) ≠ a)
    (hNext : a ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident a (C.connector k))
    (hRight : D.Incident a (C.connector (trainCyclicPred k)))
    (hAccept : C.Acceptable) :
    (C.replaceOne D k a hPrev hNext hLeft hRight).Acceptable := by
  apply C.relabelSameConnectors_acceptable D
    (C.replaceLabelAt D k a)
    (C.replaceOne D k a hPrev hNext hLeft hRight).adjacent_ne
    (C.replaceOne D k a hPrev hNext hLeft hRight).left_incident
    (C.replaceOne D k a hPrev hNext hLeft hRight).right_incident
  · intro _
    refine ⟨r, ?_⟩
    simpa [BigCycle.replaceLabelAt, hrk] using hr
  · exact hAccept

/-- Every legal one-occurrence short replacement of a cycle with at least
three occurrences preserves acceptability automatically. -/
theorem BigCycle.replaceOne_acceptable_of_three_le_length
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E)
    (hn : 3 ≤ n)
    (hPrev : C.label (trainCyclicPred k) ≠ a)
    (hNext : a ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident a (C.connector k))
    (hRight : D.Incident a (C.connector (trainCyclicPred k)))
    (hAccept : C.Acceptable) :
    (C.replaceOne D k a hPrev hNext hLeft hRight).Acceptable :=
  C.replaceOne_acceptable_of_order_ne_one D k a
    hPrev hNext hLeft hRight
    (C.twiceOrder_ne_two_of_three_le_length D hn) hAccept

/-- Finite legal short-replacement sequences which never replace r. -/
inductive BigCycle.ShortReachableAwayFrom
    (D : OrderOneData V E I P) {n : ℕ} (r : Fin n) :
    D.BigCycle n → D.BigCycle n → Prop
  | refl (C : D.BigCycle n) :
      BigCycle.ShortReachableAwayFrom D r C C
  | step (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E)
      (hrk : r ≠ k)
      (hPrev : C.label (trainCyclicPred k) ≠ a)
      (hNext : a ≠ C.label (cyclicSucc k))
      (hLeft : D.Incident a (C.connector k))
      (hRight : D.Incident a (C.connector (trainCyclicPred k)))
      {B : D.BigCycle n}
      (tail : BigCycle.ShortReachableAwayFrom D r
        (C.replaceOne D k a hPrev hNext hLeft hRight) B) :
      BigCycle.ShortReachableAwayFrom D r C B

/-- A sequence away from r keeps the literal label at r. -/
theorem BigCycle.ShortReachableAwayFrom.label_fixed
    {n : ℕ} {C B : D.BigCycle n} {r : Fin n}
    (h : BigCycle.ShortReachableAwayFrom D r C B) :
    B.label r = C.label r := by
  induction h with
  | refl C => rfl
  | @step C k a hrk hPrev hNext hLeft hRight B tail ih =>
      calc
        B.label r =
            (C.replaceOne D k a hPrev hNext hLeft hRight).label r := ih
        _ = C.label r := by
          simp [BigCycle.replaceOne, BigCycle.relabelSameConnectors,
            BigCycle.replaceLabelAt, hrk]

/-- Every finite short-replacement sequence preserves numerical order. -/
theorem BigCycle.ShortReachableAwayFrom.twiceOrder_eq
    {n : ℕ} {C B : D.BigCycle n} {r : Fin n}
    (h : BigCycle.ShortReachableAwayFrom D r C B) :
    B.twiceOrder = C.twiceOrder := by
  induction h with
  | refl C => rfl
  | @step C k a hrk hPrev hNext hLeft hRight B tail ih =>
      exact ih.trans
        (C.replaceOne_twiceOrder D k a hPrev hNext hLeft hRight)

/-- Keeping one designated occurrence fixed makes arbitrary finite legal
short replacements preserve acceptability, including at order one. -/
theorem BigCycle.ShortReachableAwayFrom.acceptable
    {n : ℕ} {C B : D.BigCycle n} {r : Fin n}
    (h : BigCycle.ShortReachableAwayFrom D r C B)
    (hr : D.designated (C.label r))
    (hAccept : C.Acceptable) :
    B.Acceptable := by
  induction h with
  | refl C => exact hAccept
  | @step C k a hrk hPrev hNext hLeft hRight B tail ih =>
      let C' := C.replaceOne D k a hPrev hNext hLeft hRight
      have hAccept' : C'.Acceptable :=
        C.replaceOne_acceptable_of_other_designated D k r a
          hrk hr hPrev hNext hLeft hRight hAccept
      have hr' : D.designated (C'.label r) := by
        simpa [C', BigCycle.replaceOne, BigCycle.relabelSameConnectors,
          BigCycle.replaceLabelAt, hrk] using hr
      exact ih hr' hAccept'

end OrderOneData
end StructuralRamsey.Girth
