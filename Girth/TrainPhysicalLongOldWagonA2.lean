import Girth.TrainA2OldWagonThree
import Girth.TrainActualFullCutLongFreshness
import Girth.TrainOneFreshLongPhysical
import Mathlib.Tactic

/-!
# Path A: an actual physical long piece cannot use an old wagon unless n=3

The earlier source-A2 lemma required the caller to supply two InWagonAt
facts at consecutive source connector positions. A genuine physical-long
replacement itself supplies exactly those facts, via its two actual
support edges and their common parent wagon.

Thus an old wagon in an actual singleton long replacement forces n=3,
and with three original geometric owner cuts every position is a cut.
This is the precise finite bridge needed before applying the already
checked all-cut supreme-plan freshness theorem.

There is no claim of having assembled the entire selected-plan geometry,
identified an arbitrary reduced plan piece, or completed cycle transfer.
No appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v w
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Genuine physical long geometry, two consecutive source vertex
connectors and source A2 force n=3 if the replacement wagon is itself
an ORIGINAL source connector. This derives the two InWagonAt premises
instead of assuming them. -/
theorem BigCycle.physicalLong_oldWagon_length_three
    {n : ℕ} (K : D.BigCycle n)
    (hn : 3 ≤ n) (hA2 : K.A2)
    (j t : Fin n) (first : E) (wagon : P) (second : E)
    (hPhysical : K.PhysicalLongGeometry D j first wagon second)
    (hOld : K.connector t = Sum.inr wagon) :
    n = 3 := by
  obtain ⟨x, y, hLeft, hRight, _hDistinct,
    hParentFirst, hParentSecond, hFirstX, hSecondY, _hNoPair⟩ :=
      hPhysical
  have hWagonLeft : K.InWagonAt wagon (trainCyclicPred j) :=
    ⟨x, hLeft, ⟨first, hParentFirst, hFirstX⟩⟩
  have hWagonRight : K.InWagonAt wagon j :=
    ⟨y, hRight, ⟨second, hParentSecond, hSecondY⟩⟩
  have hn2 : 2 ≤ n := by omega
  have hDistinctIndices : trainCyclicPred j ≠ j := by
    intro hEq
    have hSucc :=
      cyclicSucc_trainCyclicPred_of_two_le hn2 j
    rw [hEq] at hSucc
    exact (cyclicSucc_ne_self_of_two_le hn2 j) hSucc
  have hAdjacent : j = cyclicSucc (trainCyclicPred j) :=
    (cyclicSucc_trainCyclicPred_of_two_le hn2 j).symm
  exact K.old_wagon_adjacent_contacts_force_length_three
    D hn hA2 t (trainCyclicPred j) j wagon
      hOld hWagonLeft hWagonRight hDistinctIndices hAdjacent

/-- With at least three original owner changes, the only possible
old-wagon physical long case has all source connector positions cut.
Consequently the checked all-cut freshness transport can be used,
once the long piece is identified with the actual chosen plan. -/
theorem BigCycle.physicalLong_oldWagon_all_source_cuts
    {Owner : Type w} {n : ℕ} (K : D.BigCycle n)
    (hn : 3 ≤ n) (hA2 : K.A2)
    (owner : Fin n → Owner)
    (hChanges : 3 ≤ cyclicOwnerChanges owner)
    (j t : Fin n) (first : E) (wagon : P) (second : E)
    (hPhysical : K.PhysicalLongGeometry D j first wagon second)
    (hOld : K.connector t = Sum.inr wagon) :
    ∀ k : Fin n, owner k ≠ owner (cyclicSucc k) := by
  have hn3 : n = 3 :=
    K.physicalLong_oldWagon_length_three
      D hn hA2 j t first wagon second hPhysical hOld
  exact cyclicOwner_all_cut_of_length_three_three_changes
    owner hn3 hChanges

end StructuralRamsey.Girth.OrderOneData
