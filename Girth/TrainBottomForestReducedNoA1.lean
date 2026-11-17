import Girth.ForestToSupremeCycle
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

/-!
# Forest-to-supreme transfer for an actual reduced bottom cycle without A1

An actual geometrically cut-indexed witness reduct inherits A2 and A3,
but an order-one reduct need not inherit A1. A finite bottom local
forest bound supplies A1 for the TWO-occurrence case as a conclusion:
two incident labels have an allowed intersection and their two
connectors lie on one common physical edge; one is designated.
For at least three occurrences, A1 is automatic from the cycle
length / twice-order inequality. This removes an unnecessary
designated-reduct hypothesis from the bottom preservation proof.
All conclusions are GLOBAL simultaneous supreme plans.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At a bottom cut, the forest hypothesis supplies a genuine global
supreme copy for any reduced BigCycle of length at most q satisfying
A2 and A3. No A1, extra order-one labelled copy or assumed local
supreme plan is required. Repeated nonadjacent labels are allowed. -/
theorem BigCycle.hasSimultaneousSupreme_of_bottomLocalForest_A2_A3
    {n : ℕ} (C : D.BigCycle n) (H : D.BottomForestGeometry)
    (q : ℕ) (hLocal : LocalForestThrough (D.bottomForestPiece H) q)
    (hLength : n ≤ q) (hA2 : C.A2) (hA3 : C.A3) :
    C.HasSimultaneousSupreme := by
  classical
  have hForest : C.BottomForest D H :=
    C.bottomForest_of_localForest D H q hLocal hLength
  by_cases hn : n = 2
  · subst n
    let a : Set.range C.label := ⟨C.label 0, ⟨0, rfl⟩⟩
    let b : Set.range C.label := ⟨C.label 1, ⟨1, rfl⟩⟩
    have hab : a ≠ b := by
      intro h
      have hVal := congrArg Subtype.val h
      exact C.adjacent_ne 0
        (by simpa [a, b, cyclicSucc] using hVal)
    exact C.hasSimultaneousSupreme_of_two_bottom_forest
      D H (hForest.pairwiseAllowed hab)
  · have hn3 : 3 ≤ n := by
      have hge := C.length_ge_two
      omega
    have hA1 : C.A1 := by
      intro hOrder
      have hLengthLe := C.length_le_twiceOrder
      omega
    exact C.hasSimultaneousSupreme_of_bottomForest
      D H ⟨hA1, hA2, hA3⟩ hForest

end StructuralRamsey.Girth.OrderOneData
