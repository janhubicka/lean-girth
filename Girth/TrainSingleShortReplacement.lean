import Girth.TrainShortReplacementGlobal

/-!
# Circulation: one globally legal short replacement

Short replacements do not change connectors.  Replacing one occurrence at a
time therefore needs only the genuinely local legality checks: the new label
must differ from its two cyclic neighbours and must be incident with the two
unchanged boundary connectors.

The resulting word is a literal BigCycle.  Its order, A2 and A3 are inherited
from the original cycle.  At order one, retaining any other designated
occurrence discharges A1.  This is the iterative kernel used by the circulation
cycle-transfer proof; it does not choose the replacement edge itself.
-/

namespace StructuralRamsey.Girth

/-- Cyclic predecessor and successor are inverse once the cycle has at least
two positions. -/
theorem trainCyclicPred_cyclicSucc_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    trainCyclicPred (cyclicSucc i) = i := by
  apply Fin.ext
  simp [trainCyclicPred, cyclicSucc]
  omega

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The label function obtained by changing one cyclic occurrence. -/
noncomputable def BigCycle.replaceLabelAt
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (a : I ⊕ E) :
    Fin n → I ⊕ E :=
  Function.update C.label k a

/-- Two neighbour inequalities and the two boundary incidences are enough to
turn a one-occurrence short replacement into a genuine BigCycle. -/
noncomputable def BigCycle.replaceOne
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
      simp [BigCycle.replaceLabelAt, Function.update_same,
        Function.update_noteq hsk, hNext]
    · by_cases hsk : cyclicSucc i = k
      · have hip : i = trainCyclicPred k := by
          have h := congrArg trainCyclicPred hsk
          rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at h
          exact h
        simp [BigCycle.replaceLabelAt, Function.update_noteq hik,
          hsk, hip, hPrev]
      · simpa [BigCycle.replaceLabelAt, Function.update_noteq hik,
          Function.update_noteq hsk] using C.adjacent_ne i
  · intro i
    by_cases hik : i = k
    · subst i
      simpa [BigCycle.replaceLabelAt] using hLeft
    · simpa [BigCycle.replaceLabelAt, Function.update_noteq hik]
        using C.left_incident i
  · intro i
    by_cases hsk : cyclicSucc i = k
    · have hip : i = trainCyclicPred k := by
        have h := congrArg trainCyclicPred hsk
        rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at h
        exact h
      simpa [BigCycle.replaceLabelAt, hsk, hip] using hRight
    · simpa [BigCycle.replaceLabelAt, Function.update_noteq hsk]
        using C.right_incident i

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
preserves acceptability even at order one.  This is the form used when a
chosen supreme copy is kept while the other occurrences are replaced. -/
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
    simpa [BigCycle.replaceLabelAt, Function.update_noteq hrk] using hr
  · exact hAccept

end OrderOneData
end StructuralRamsey.Girth
