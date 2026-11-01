import Girth.TrainCyclicOwnerFinListBridge
import Girth.TrainOneDoubleWordSplit
import Girth.TrainCyclicOwnerIsolatedNonincrease

/-!
# Actual cyclic owner-cut bound for one doubled source occurrence

The source K is given by a Fin-indexed cyclic owner function. A
long insertion replaces exactly one owner entry by two successive
copies of a receiving owner target.

The proof factors the operation into (1) changing the old owner's
value at that position, and (2) duplicating the new target once.
The first operation cannot increase cuts at an isolated owner
(#726, already kernel checked). The second is an EXACT equality
on cyclic List cuts (#750), and #751 identifies those with the
actual Finset number of owner changes.

This is a finite owner-word theorem with no physical geometry.
The remaining Path A step is to supply a real output owner function
whose literal word is the doubled owner word and prove its
geometric admissibility. No appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} [DecidableEq Owner]

/-- The actual one-double word is unaffected by first replacing
the source owner at the doubled position, since that old entry is
overwritten by the same target pair. -/
theorem oneDoubleWord_of_reassigned_owner
    {n : ℕ} (owner : Fin n → Owner)
    (j : Fin n) (target : Owner) :
    oneDoubleWord (cyclicReplaceOwner owner j target) j target target =
      oneDoubleWord owner j target target := by
  let changed := cyclicReplaceOwner owner j target
  have hBlocks :
      (fun k : Fin n =>
        if k = j then [target, target] else [changed k]) =
      (fun k : Fin n =>
        if k = j then [target, target] else [owner k]) := by
    funext k
    by_cases hk : k = j
    · simp [hk]
    · simp [hk, changed, cyclicReplaceOwner]
  exact congrArg List.flatten (congrArg List.ofFn hBlocks)

/-- The cyclic cut count of a one-double owner word equals the
actual Fin-indexed cut count after one FIXED-LENGTH reassignment.
This equality works for arbitrary target choices and any index,
including the wrap; isolation is not needed for this identity. -/
theorem oneDoubleWord_cyclicCuts_eq_reassigned
    {n : ℕ} (owner : Fin n → Owner)
    (j : Fin n) (target : Owner) :
    listCyclicOwnerChanges (oneDoubleWord owner j target target) =
      cyclicOwnerChanges (cyclicReplaceOwner owner j target) := by
  let changed := cyclicReplaceOwner owner j target
  have hAt : changed j = target := by
    simp [changed, cyclicReplaceOwner]
  obtain ⟨before, after, hSource, hOutput⟩ :=
    oneDoubleWord_exists_common_split changed j target target
  have hWord : oneDoubleWord changed j target target =
      oneDoubleWord owner j target target :=
    oneDoubleWord_of_reassigned_owner owner j target
  calc
    listCyclicOwnerChanges (oneDoubleWord owner j target target) =
        listCyclicOwnerChanges (oneDoubleWord changed j target target) :=
          congrArg listCyclicOwnerChanges hWord.symm
    _ = listCyclicOwnerChanges (before ++ target :: target :: after) := by
          rw [hOutput]
    _ = listCyclicOwnerChanges (before ++ target :: after) :=
          listCyclicOwnerChanges_duplicate before after target
    _ = listCyclicOwnerChanges (List.ofFn changed) := by
          rw [hSource, hAt]
    _ = cyclicOwnerChanges changed :=
          (cyclicOwnerChanges_eq_listCyclicOwnerChanges changed).symm

/-- With two old incident cuts at an isolated source owner, one
doubled target pair cannot increase the number of cyclic cuts. -/
theorem oneDoubleWord_cyclicCuts_le_of_isolated
    {n : ℕ} (hn : 2 ≤ n)
    (owner : Fin n → Owner) (j : Fin n) (target : Owner)
    (hPrev : owner (trainCyclicPred j) ≠ owner j)
    (hNext : owner j ≠ owner (cyclicSucc j)) :
    listCyclicOwnerChanges (oneDoubleWord owner j target target) ≤
      cyclicOwnerChanges owner := by
  calc
    listCyclicOwnerChanges (oneDoubleWord owner j target target) =
        cyclicOwnerChanges (cyclicReplaceOwner owner j target) :=
          oneDoubleWord_cyclicCuts_eq_reassigned owner j target
    _ ≤ cyclicOwnerChanges owner :=
          cyclicOwnerChanges_replace_isolated_le
            hn owner j target hPrev hNext

/-- The Fin-indexed n-to-(n+1) output owner theorem: IF the
actual output owner sequence has the exact doubled literal word,
its genuine cyclic cut count cannot exceed that of the isolated
original owner. Nothing is inferred from label provenance alone. -/
theorem cyclicOwnerChanges_long_output_le
    {n m : ℕ} (hn : 2 ≤ n)
    (owner : Fin n → Owner)
    (outOwner : Fin m → Owner)
    (j : Fin n) (target : Owner)
    (hPrev : owner (trainCyclicPred j) ≠ owner j)
    (hNext : owner j ≠ owner (cyclicSucc j))
    (hWord : List.ofFn outOwner =
      oneDoubleWord owner j target target) :
    cyclicOwnerChanges outOwner ≤ cyclicOwnerChanges owner := by
  calc
    cyclicOwnerChanges outOwner =
        listCyclicOwnerChanges (List.ofFn outOwner) :=
          cyclicOwnerChanges_eq_listCyclicOwnerChanges outOwner
    _ = listCyclicOwnerChanges
        (oneDoubleWord owner j target target) := by rw [hWord]
    _ ≤ cyclicOwnerChanges owner :=
          oneDoubleWord_cyclicCuts_le_of_isolated
            hn owner j target hPrev hNext

end StructuralRamsey.Girth
