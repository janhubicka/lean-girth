import Mathlib.Tactic

/-!
# Duplicating a cyclic owner does not create new cyclic cuts

The designated long insertion replaces one source occurrence by
TWO consecutive occurrences owned by the same attached standard.
The owner cut computation splits into:
* reassign the isolated original owner to that standard (already
  verified by TrainCyclicOwnerIsolatedNonincrease);
* duplicate its new owner exactly once.

This file formalizes the SECOND step for arbitrary finite cyclic
LIST words, including insertion at the start or end and all wraps.
It is independent of the chosen standard and physical geometry.
Connecting List.ofFn owners to the actual Fin-indexed cyclic owner
cut count is a separate bridge, not claimed here.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner : Type v} [DecidableEq Owner]

/-- The cut indicator of two neighbouring owner labels. -/
def ownerCutStep (x y : Owner) : ℕ :=
  if x = y then 0 else 1

@[simp] theorem ownerCutStep_self (x : Owner) :
    ownerCutStep x x = 0 := by
  simp [ownerCutStep]

/-- Count successive changes while walking from a chosen entering
owner through the word and then back to a specified exit owner.
The special case enter=exit and word beginning with enter is the
usual cyclic cut number. -/
def ownerWalkCuts (enter : Owner) : List Owner → Owner → ℕ
  | [], exit => ownerCutStep enter exit
  | x :: xs, exit =>
      ownerCutStep enter x + ownerWalkCuts x xs exit

/-- Every adjacent pair in a nonempty cyclic word is counted once,
including the final-to-initial boundary. -/
def listCyclicOwnerChanges : List Owner → ℕ
  | [] => 0
  | first :: rest => ownerWalkCuts first (first :: rest) first

/-- Duplicating one owner leaves an arbitrary closed or open walk's
number of changes unchanged: the only new edge is target-to-target. -/
theorem ownerWalkCuts_duplicate
    (enter exit target : Owner) (before after : List Owner) :
    ownerWalkCuts enter (before ++ target :: target :: after) exit =
      ownerWalkCuts enter (before ++ target :: after) exit := by
  induction before generalizing enter with
  | nil =>
      simp [ownerWalkCuts]
  | cons first before ih =>
      simpa only [List.cons_append, ownerWalkCuts] using
        congrArg (fun z => ownerCutStep enter first + z) (ih first)

/-- The number of CYCLIC owner cuts is invariant when one owner
is duplicated consecutively, for ALL original positions. -/
theorem listCyclicOwnerChanges_duplicate
    (before after : List Owner) (target : Owner) :
    listCyclicOwnerChanges (before ++ target :: target :: after) =
      listCyclicOwnerChanges (before ++ target :: after) := by
  cases before with
  | nil =>
      simp [listCyclicOwnerChanges, ownerWalkCuts]
  | cons first rest =>
      change ownerWalkCuts first
        ((first :: rest) ++ target :: target :: after) first =
        ownerWalkCuts first ((first :: rest) ++ target :: after) first
      exact ownerWalkCuts_duplicate first first target
        (first :: rest) after

end StructuralRamsey.Girth
