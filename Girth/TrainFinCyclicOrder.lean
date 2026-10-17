import Girth.TrainCyclicListOrder
import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Circulation: identify cyclic List weight with indexed BigCycle order

The manuscript's BigCycle order is a finite sum of the twice-weight
of each right connector and its cyclic successor. The same sum can be
read from the physical ordered connector List, zipped against its
one-step rotation. The preceding List lemma identifies this sum
with cyclicKindTwiceWeight.

This is the finite-indexed conversion needed for numerical invariance
of actual mixed replacement outputs. No geometry, extra axioms,
appendix theorem, or replacement-plan hypothesis is used.
-/

namespace StructuralRamsey.Girth

/-- The weighted one-step rotation of an indexed connector sequence
is exactly the List.ofFn of its cyclic successor pair weights. -/
theorem zipKindRotate_ofFn
    {n : ℕ} (f : Fin n → CycleConnectorKind) :
    List.zipWith twiceOccurrenceWeight
        (List.ofFn f) ((List.ofFn f).rotate 1) =
      List.ofFn (fun i : Fin n =>
        twiceOccurrenceWeight (f i) (f (cyclicSucc i))) := by
  let xs := List.ofFn f
  have hLen :
      (List.zipWith twiceOccurrenceWeight xs (xs.rotate 1)).length = n := by
    simp [xs]
  have hLenR :
      (List.ofFn (fun i : Fin n =>
        twiceOccurrenceWeight (f i) (f (cyclicSucc i)))).length = n := by
    simp
  apply List.ext_getElem (by rw [hLen, hLenR])
  intro i hLeft hRight
  have hi : i < n := by simpa [hLenR] using hRight
  have hxi : i < xs.length := by simpa [xs] using hi
  have hRotIndex : i < (xs.rotate 1).length := by
    simpa using hxi
  have hX :
      xs[i]? = some (f ⟨i, hi⟩) := by
    rw [List.getElem?_eq_getElem hxi]
    simp [xs, List.get_ofFn]
  have hRotate :
      (xs.rotate 1)[i]? =
        some (f (cyclicSucc ⟨i, hi⟩)) := by
    rw [List.getElem?_eq_getElem hRotIndex]
    have hGet := List.get_rotate_one xs ⟨i, hRotIndex⟩
    simpa [xs, List.get_ofFn, cyclicSucc] using
      congrArg some hGet
  have hZip :
      (List.zipWith twiceOccurrenceWeight xs (xs.rotate 1))[i]? =
        some (twiceOccurrenceWeight
          (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := by
    rw [List.getElem?_zipWith, hX, hRotate]
  have hOfFn :
      (List.ofFn (fun j : Fin n =>
        twiceOccurrenceWeight (f j) (f (cyclicSucc j))))[i]? =
          some (twiceOccurrenceWeight
            (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := by
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp [List.get_ofFn]
  apply Option.some.inj
  calc
    some ((List.zipWith twiceOccurrenceWeight xs (xs.rotate 1))[i]) =
        (List.zipWith twiceOccurrenceWeight xs (xs.rotate 1))[i]? :=
          (List.getElem?_eq_getElem hLeft).symm
    _ = some (twiceOccurrenceWeight
          (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := hZip
    _ = (List.ofFn (fun j : Fin n =>
          twiceOccurrenceWeight (f j) (f (cyclicSucc j))))[i]? :=
          hOfFn.symm
    _ = some ((List.ofFn (fun j : Fin n =>
          twiceOccurrenceWeight (f j) (f (cyclicSucc j))))[i]) :=
          List.getElem?_eq_getElem hRight

/-- Exact equivalence between the finite cyclic weight of a List.ofFn
and the naturally indexed cyclic weighted sum. -/
theorem cyclicKindTwiceWeight_ofFn
    {n : ℕ} (f : Fin n → CycleConnectorKind) :
    cyclicKindTwiceWeight (List.ofFn f) =
      ∑ i : Fin n,
        twiceOccurrenceWeight (f i) (f (cyclicSucc i)) := by
  rw [cyclicKindTwiceWeight_eq_zipRotate,
    zipKindRotate_ofFn f]
  exact List.sum_ofFn

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The actual numeric twice-order of a BigCycle equals the cyclic
List twice-weight of its connector types in literal occurrence order. -/
theorem BigCycle.twiceOrder_eq_cyclicKindList
    {n : ℕ} (C : D.BigCycle n) :
    C.twiceOrder =
      cyclicKindTwiceWeight
        (List.ofFn (fun i : Fin n =>
          connectorKind (C.connector i))) := by
  symm
  exact cyclicKindTwiceWeight_ofFn
    (fun i : Fin n => connectorKind (C.connector i))

end OrderOneData
end StructuralRamsey.Girth
