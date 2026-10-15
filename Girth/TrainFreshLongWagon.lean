import Girth.TrainShortReplacementNeighbour
import Girth.TrainSimultaneousSupreme

/-!
# Circulation: two long replacements cannot insert one fresh wagon

An inserted long-piece wagon is absent from the original connector word.
A3 therefore confines ALL original vertices of that wagon to two successive
connector positions. A legitimate long piece from occurrence j has both its
original boundary positions there, namely predecessor(j) and j.

At length at least three this determines j uniquely: two different
occurrences cannot both have their two original boundaries in the same
two-position window. Therefore distinct long replacements cannot insert the
same fresh wagon.

This proves an important part of global connector injectivity for the
manuscript's admissible-replacement lemma, without assuming wagon linearity,
an output system-girth bound, or the existence of a global replacement cycle.
Other long-piece legality and supreme-plan composition remain separate.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Under A3, a nonconnector wagon containing BOTH boundary vertex
positions of an occurrence determines that occurrence uniquely, for
big cycles of length at least three. -/
theorem BigCycle.nonconnector_wagon_boundary_occurrence_unique
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (p : P)
    (hNoConnector : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i j : Fin n)
    (hiPrev : C.InWagonAt p (trainCyclicPred i))
    (hiHere : C.InWagonAt p i)
    (hjPrev : C.InWagonAt p (trainCyclicPred j))
    (hjHere : C.InWagonAt p j) :
    i = j := by
  obtain ⟨t, hWindow⟩ := hAccept.2.2 p hNoConnector
  have hOcc (r : Fin n)
      (hPrev : C.InWagonAt p (trainCyclicPred r))
      (hHere : C.InWagonAt p r) : r = cyclicSucc t := by
    have hPr := hWindow (trainCyclicPred r) hPrev
    have hR := hWindow r hHere
    rcases hR with hRt | hRs
    · rcases hPr with hPt | hPs
      · have hPredEq : trainCyclicPred r = r := hPt.trans hRt.symm
        have hs := congrArg cyclicSucc hPredEq
        rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two r] at hs
        exact False.elim (by
          have hSelf : cyclicSucc r ≠ r := by
            intro hr
            exact C.adjacent_ne r (congrArg C.label hr.symm)
          exact hSelf hs.symm)
      · have hImpossible : trainCyclicPred t = cyclicSucc t := by
          rw [hRt] at hPs
          exact hPs
        exact False.elim ((trainCyclicPred_ne_cyclicSucc_of_three_le hn t)
          hImpossible)
    · exact hRs
  exact (hOcc i hiPrev hiHere).trans (hOcc j hjPrev hjHere).symm

/-- Two distinct long pieces with the same fresh wagon are impossible.
The pieces may be chosen for different labels: only the old connector
geometry and their genuine source-edge incidences are used. -/
theorem BigCycle.longPieces_fresh_wagon_distinct
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (p : P) (hNoConnector : ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (a b : Fin n) (hab : a ≠ b)
    (u v : Fin n) (e f g h : E)
    (hFirst : C.LongValid D u a e p f)
    (hSecond : C.LongValid D v b g p h) : False := by
  obtain ⟨x, y, hAx, hAy, _he, _hf, _hef, hew, hfw,
    hxe, hyf, _hNoPair⟩ := hFirst
  obtain ⟨z, w, hBz, hBw, _hg, _hh, _hgh, hgw, hhw,
    hzg, hwh, _hNoPair2⟩ := hSecond
  have hiPrev : C.InWagonAt p (trainCyclicPred a) :=
    ⟨x, hAx, e, hew, hxe⟩
  have hiHere : C.InWagonAt p a :=
    ⟨y, hAy, f, hfw, hyf⟩
  have hjPrev : C.InWagonAt p (trainCyclicPred b) :=
    ⟨z, hBz, g, hgw, hzg⟩
  have hjHere : C.InWagonAt p b :=
    ⟨w, hBw, h, hhw, hwh⟩
  exact hab (C.nonconnector_wagon_boundary_occurrence_unique D
    hAccept hn p hNoConnector a b hiPrev hiHere hjPrev hjHere)

end StructuralRamsey.Girth.OrderOneData
