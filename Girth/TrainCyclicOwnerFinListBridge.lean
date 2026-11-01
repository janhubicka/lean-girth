import Girth.TrainCyclicDuplicateOwnerWord
import Girth.TrainFinCyclicOrder
import Girth.TrainMinimalCyclicOwners
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Exact equality of the Fin-indexed and List cyclic owner cut counts

The original cycle's geometric owner minimizer uses the number of
genuine cyclic cut positions as a Finset cardinal. The new doubled
owner certificate is a literal List.ofFn word. This module gives
the precise bridge between the two notions of cyclic cut count,
including the final-to-initial wrap. This allows the verified
fixed-length isolation lemma and the new list-duplication theorem
to be composed without silently changing the counting definition.

The mathematical content is independent of the choice of standard
and of the literal physical edges. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} [DecidableEq Owner]

/-- The open walk's cut sum is the zip sum with its entering and
exiting boundary positions included once. -/
theorem ownerWalkCuts_eq_zip
    (enter exit : Owner) (tail : List Owner) :
    ownerWalkCuts enter tail exit =
      (List.zipWith ownerCutStep
        (enter :: tail) (tail ++ [exit])).sum := by
  induction tail generalizing enter with
  | nil =>
      simp [ownerWalkCuts]
  | cons x xs ih =>
      simpa [ownerWalkCuts, List.zipWith] using
        congrArg (fun z => ownerCutStep enter x + z) (ih x)

/-- A cyclic word of owners counts exactly the edges of its
one-position rotation, including the final-to-first transition. -/
theorem listCyclicOwnerChanges_eq_zipRotate
    (word : List Owner) :
    listCyclicOwnerChanges word =
      (List.zipWith ownerCutStep word (word.rotate 1)).sum := by
  cases word with
  | nil => rfl
  | cons first tail =>
      have hRotate : (first :: tail).rotate 1 = tail ++ [first] := by
        simpa using (List.rotate_cons_succ tail first 0)
      have hWalk := ownerWalkCuts_eq_zip first first tail
      simpa [listCyclicOwnerChanges, ownerWalkCuts, hRotate] using hWalk

/-- The same index-by-index rotation argument already used for
the verified twice-order weights works for arbitrary owner cuts. -/
theorem zipOwnerCutRotate_ofFn
    {n : ℕ} (f : Fin n → Owner) :
    List.zipWith ownerCutStep
        (List.ofFn f) ((List.ofFn f).rotate 1) =
      List.ofFn (fun i : Fin n =>
        ownerCutStep (f i) (f (cyclicSucc i))) := by
  let xs := List.ofFn f
  have hLen :
      (List.zipWith ownerCutStep xs (xs.rotate 1)).length = n := by
    simp [xs]
  have hLenR :
      (List.ofFn (fun i : Fin n =>
        ownerCutStep (f i) (f (cyclicSucc i)))).length = n := by
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
      (List.zipWith ownerCutStep xs (xs.rotate 1))[i]? =
        some (ownerCutStep
          (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := by
    rw [List.getElem?_zipWith, hX, hRotate]
  have hOfFn :
      (List.ofFn (fun j : Fin n =>
        ownerCutStep (f j) (f (cyclicSucc j))))[i]? =
          some (ownerCutStep
            (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := by
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp [List.get_ofFn]
  apply Option.some.inj
  calc
    some ((List.zipWith ownerCutStep xs (xs.rotate 1))[i]) =
        (List.zipWith ownerCutStep xs (xs.rotate 1))[i]? :=
          (List.getElem?_eq_getElem hLeft).symm
    _ = some (ownerCutStep
          (f ⟨i, hi⟩) (f (cyclicSucc ⟨i, hi⟩))) := hZip
    _ = (List.ofFn (fun j : Fin n =>
          ownerCutStep (f j) (f (cyclicSucc j))))[i]? :=
          hOfFn.symm
    _ = some ((List.ofFn (fun j : Fin n =>
          ownerCutStep (f j) (f (cyclicSucc j))))[i]) :=
          List.getElem?_eq_getElem hRight


/-- The genuine Finset count equals the sum of elementary
disequality cut indicators, with no assuming finite owner types. -/
theorem cyclicOwnerChanges_eq_sum_ownerCutStep
    {n : ℕ} (owner : Fin n → Owner) :
    cyclicOwnerChanges owner =
      ∑ i : Fin n, ownerCutStep (owner i) (owner (cyclicSucc i)) := by
  classical
  simp [cyclicOwnerChanges, ownerCutStep, Finset.sum_ite]

/-- Exact bridge between actual Fin-indexed geometric owner cuts and
the cyclic List cut count of their literal occurrence word. -/
theorem cyclicOwnerChanges_eq_listCyclicOwnerChanges
    {n : ℕ} (owner : Fin n → Owner) :
    cyclicOwnerChanges owner =
      listCyclicOwnerChanges (List.ofFn owner) := by
  rw [listCyclicOwnerChanges_eq_zipRotate,
    zipOwnerCutRotate_ofFn owner, List.sum_ofFn]
  exact cyclicOwnerChanges_eq_sum_ownerCutStep owner

end StructuralRamsey.Girth
