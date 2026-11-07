import Girth.TrainActualTwoCutShortSingletonOrientation
import Girth.TrainCyclicRunIndexReverseWindow
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a two-cut singleton run has exactly one original source occurrence

Suppose the two genuinely distinct original owner cuts are indexed by
Fin 2, and the run ending at indexed cut j is forward-adjacent to its
previous cut. The checked reverse run-fibre lemma says the ONLY original
source occurrence assigned to j is the cut-ending position p.

Every other original source occurrence has the other run index
pred(j). Consequently its actual GEOMETRIC owner equals the owner at
the other indexed cut, including the cyclic wrap. This supplies the
hKeep premise needed for a one-short/all-keep standard-local transfer
once the chosen reduced standard is the longer owner run.

No source B-label identity, physical edge, replacement plan or global
supreme conclusion is assumed or constructed here.
-/

namespace StructuralRamsey.Girth

universe v

/-- In an EXACT two-cut cyclic owner word, if the j run is a
singleton, every original position other than its cut-ending
position is owned by the OTHER reduced owner. -/
theorem cyclicOwner_two_cut_singleton_complement_owner
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hn : 2 ≤ n)
    (hTwo : cyclicOwnerChanges owner = 2)
    (j : Fin (cyclicOwnerChanges owner))
    (hForward : cyclicOwnerCutIndex owner j =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred j)))
    (x : Fin n)
    (hx : x ≠ cyclicOwnerCutIndex owner j) :
    owner x =
      owner (cyclicOwnerCutIndex owner (trainCyclicPred j)) := by
  have hPos : 0 < cyclicOwnerChanges owner := by omega
  let p := cyclicOwnerCutIndex owner j
  have hPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred p := by
    dsimp [p]
    rw [hForward]
    exact (trainCyclicPred_cyclicSucc_of_two_le hn
      (cyclicOwnerCutIndex owner (trainCyclicPred j))).symm
  have hRunNe : cyclicOwnerRunIndex owner hPos x ≠ j := by
    intro hRun
    have hAt : x = p :=
      cyclicOwnerRunIndex_singleton_fibre
        owner hn (by omega : 2 ≤ cyclicOwnerChanges owner)
        j p x hPrev rfl hRun
    exact hx hAt
  have hOtherNe : trainCyclicPred j ≠ j := by
    have hPredSucc := trainCyclicPred_eq_cyclicSucc_of_card_two hTwo j
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

end StructuralRamsey.Girth
