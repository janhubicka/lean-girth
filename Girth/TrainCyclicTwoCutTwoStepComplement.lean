import Girth.TrainActualTwoStepCutOrientation
import Girth.TrainActualTwoCutDistinctStandards
import Girth.TrainCyclicRunIndexReverseWindow
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: the exact two-cut two-step run and its complementary owner

For the actual cyclic owner word with exactly two changes, suppose
one run is bounded by original cut positions pred(t) and succ(t).
The generalized reverse run-fibre theorem proves that this run
consists only of the TWO source occurrences t, succ(t), including
cyclic wrap.

Every original source occurrence outside those two positions is
therefore owned by the OTHER reduced owner (at cut index pred(j)).
This is precisely the hKeep condition for an original physical
two-short replacement around the existing wagon at connector t.
No physical edge, original designated label, or supreme plan is
postulated by this finite kernel. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
universe v

/-- An index of a two-element cyclic cut set is either a given
index or its predecessor; no third cut can be hidden at the wrap. -/
theorem finTwo_eq_self_or_pred
    {n : ℕ} (hTwo : n = 2) (j k : Fin n) :
    k = j ∨ k = trainCyclicPred j := by
  subst n
  fin_cases j <;> fin_cases k <;> decide

/-- With exactly TWO geometric owner cuts, a two-step run ending at
cut j has exactly t and succ(t) in its original source fibre.
Every other position has the OTHER cut owner's geometric label. -/
theorem cyclicOwner_two_cut_two_step_complement_owner
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hn : 3 ≤ n)
    (hTwo : cyclicOwnerChanges owner = 2)
    (j : Fin (cyclicOwnerChanges owner))
    (t x : Fin n)
    (hPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred t)
    (hHere : cyclicOwnerCutIndex owner j = cyclicSucc t)
    (hx : x ≠ t)
    (hxNext : x ≠ cyclicSucc t) :
    owner x =
      owner (cyclicOwnerCutIndex owner (trainCyclicPred j)) := by
  have hPos : 0 < cyclicOwnerChanges owner := by omega
  have hRunNe : cyclicOwnerRunIndex owner hPos x ≠ j := by
    intro hRun
    rcases cyclicOwnerRunIndex_two_step_fibre_of_two_le
      owner hn (by omega : 2 ≤ cyclicOwnerChanges owner)
      j t x hPrev hHere hRun with hAt | hAt
    · exact hx hAt
    · exact hxNext hAt
  have hOtherNe : trainCyclicPred j ≠ j := by
    have hPredSucc :=
      trainCyclicPred_eq_cyclicSucc_of_card_two hTwo j
    rw [hPredSucc]
    exact cyclicSucc_ne_self_of_two_le
      (by omega : 2 ≤ cyclicOwnerChanges owner) j
  have hRunEq :
      cyclicOwnerRunIndex owner hPos x = trainCyclicPred j := by
    apply Fin.ext
    have hRunVal := (cyclicOwnerRunIndex owner hPos x).isLt
    have hPredVal := (trainCyclicPred j).isLt
    have hjVal := j.isLt
    have hRunNeVal :
        (cyclicOwnerRunIndex owner hPos x).val ≠ j.val := by
      intro h
      exact hRunNe (Fin.ext h)
    have hOtherNeVal : (trainCyclicPred j).val ≠ j.val := by
      intro h
      exact hOtherNe (Fin.ext h)
    omega
  calc
    owner x =
      owner (cyclicOwnerCutIndex owner
        (cyclicOwnerRunIndex owner hPos x)) :=
      cyclicOwnerRunIndex_owner_eq_cut owner hPos x
    _ = owner (cyclicOwnerCutIndex owner (trainCyclicPred j)) := by
      rw [hRunEq]


/-- If an existing wagon is at an UNCUT original position t, with the
two neighboring positions both genuine owner cuts, the canonical
owner run ending at succ(t) is the two-step run {t,succ(t)}.
At EXACTLY two cuts every other original source position belongs
to the opposite reduced owner's run. This canonical orientation
does not depend on which reduced standard was originally chosen. -/
theorem cyclicOwner_two_cut_old_wagon_oriented_run
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hn : 3 ≤ n)
    (hTwo : cyclicOwnerChanges owner = 2)
    (t : Fin n)
    (hPrevious : trainCyclicPred t ∈ cyclicOwnerCutPositions owner)
    (hNext : cyclicSucc t ∈ cyclicOwnerCutPositions owner)
    (hUncut : t ∉ cyclicOwnerCutPositions owner) :
    ∃ cut : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner cut = cyclicSucc t ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred t ∧
      (∀ x : Fin n, x ≠ t → x ≠ cyclicSucc t →
        owner x =
          owner (cyclicOwnerCutIndex owner (trainCyclicPred cut))) := by
  obtain ⟨cut, hHere, hPrev⟩ :=
    cyclicOwnerCutIndex_pred_of_single_uncut_gap
      owner hn t hPrevious hNext hUncut
  refine ⟨cut, hHere, hPrev, ?_⟩
  intro x hx hxNext
  exact cyclicOwner_two_cut_two_step_complement_owner
    owner hn hTwo cut t x hPrev hHere hx hxNext


namespace OrderOneData
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In a genuine two-cut source, a wagon connector containing
the two ORIGINAL cut-boundary vertices is necessarily an UNCUT
source connector: the only two owner-cut indices are cut and
pred(cut), and both of their connectors are vertices. -/
theorem BigCycle.old_wagon_at_two_vertex_cuts_is_uncut
    {Owner : Type v} {n : ℕ}
    (K : D.BigCycle n)
    (owner : Fin n → Owner)
    (hTwo : cyclicOwnerChanges owner = 2)
    (cut : Fin (cyclicOwnerChanges owner))
    (w : P)
    (hAtA : K.InWagonAt w
      (cyclicOwnerCutIndex owner (trainCyclicPred cut)))
    (hAtB : K.InWagonAt w (cyclicOwnerCutIndex owner cut))
    (t : Fin n) (hOld : K.connector t = Sum.inr w) :
    t ∉ cyclicOwnerCutPositions owner := by
  intro hCut
  obtain ⟨j, hj⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner t).mp hCut
  rcases finTwo_eq_self_or_pred hTwo cut j with hjCut | hjPred
  · rw [hjCut] at hj
    obtain ⟨z, hz, _⟩ := hAtB
    have hBad : (Sum.inl z : V ⊕ P) = Sum.inr w := by
      calc
        Sum.inl z = K.connector (cyclicOwnerCutIndex owner cut) := hz.symm
        _ = K.connector t := congrArg K.connector hj
        _ = Sum.inr w := hOld
    cases hBad
  · rw [hjPred] at hj
    obtain ⟨z, hz, _⟩ := hAtA
    have hBad : (Sum.inl z : V ⊕ P) = Sum.inr w := by
      calc
        Sum.inl z =
          K.connector (cyclicOwnerCutIndex owner (trainCyclicPred cut)) :=
            hz.symm
        _ = K.connector t := congrArg K.connector hj
        _ = Sum.inr w := hOld
    cases hBad

end OrderOneData

end StructuralRamsey.Girth
