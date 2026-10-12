import Mathlib.Tactic

/-!
# Finite A2 edge-pruning obstruction with unchanged wagon carrier

A fixed order-three cycle in the circulation manuscript has the side
vertices x=0 and y=1 incident to a wagon W whose old edge labels are
f1={0,2}, f2={1,3}, and d={0,1}. Removing only d leaves the wagon's
vertex carrier unchanged but switches the A2 no-common-ambient-edge
condition from false to true. We encode the five physical edges on
{x,y,a,b,c} and make every step decidable.

This checks the *no-common-edge clause* of A2, and linearity of the
physical edges. It does not assert complete pretrain system-Girth
or introduce a full formal syntax for acceptable big cycles.
-/

namespace StructuralRamsey.Girth

/-- The physical vertices are x=0, y=1, a=2, b=3 and c=4. -/
abbrev PruningVertex := Fin 5

def pruningF0 : Finset PruningVertex := {0, 4}
def pruningF1 : Finset PruningVertex := {0, 2}
def pruningF2 : Finset PruningVertex := {1, 3}
def pruningF3 : Finset PruningVertex := {1, 4}
def pruningChord : Finset PruningVertex := {0, 1}

def pruningOldEdges : Finset (Finset PruningVertex) :=
  {pruningF0, pruningF1, pruningF2, pruningF3, pruningChord}

def pruningNewEdges : Finset (Finset PruningVertex) :=
  {pruningF0, pruningF1, pruningF2, pruningF3}

/-- The distinguished connector wagon W uses f1, f2 and initially d. -/
def pruningOldWagon : Finset (Finset PruningVertex) :=
  {pruningF1, pruningF2, pruningChord}

def pruningNewWagon : Finset (Finset PruningVertex) :=
  {pruningF1, pruningF2}

/-- Two different edges have at most one common vertex. -/
def pruningLinear (E : Finset (Finset PruningVertex)) : Prop :=
  (E.all (fun e =>
    E.all (fun f => decide (e = f ∨ (e ∩ f).card ≤ 1)))) = true

/-- The A2 restriction for the two side vertex connectors 0 and 1. -/
def pruningA2SideCondition (E : Finset (Finset PruningVertex)) : Prop :=
  (E.all (fun e =>
    decide (¬ ((0 : PruningVertex) ∈ e ∧ (1 : PruningVertex) ∈ e)))) = true

theorem pruning_old_new_linear :
    pruningLinear pruningOldEdges ∧ pruningLinear pruningNewEdges := by
  unfold pruningLinear pruningOldEdges pruningNewEdges
    pruningF0 pruningF1 pruningF2 pruningF3 pruningChord
  decide

/-- Even deleting the chord from W does not change its carrier. -/
theorem pruning_wagon_carriers_identical :
    pruningOldWagon.biUnion id = pruningNewWagon.biUnion id := by
  decide

/-- The A2 side-edge condition changes although the connector carrier does not. -/
theorem pruning_A2_toggles :
    ¬ pruningA2SideCondition pruningOldEdges ∧
      pruningA2SideCondition pruningNewEdges := by
  unfold pruningA2SideCondition pruningOldEdges pruningNewEdges
    pruningF0 pruningF1 pruningF2 pruningF3 pruningChord
  decide

/-- All four remaining cycle edges survive and the extra chord vanishes. -/
theorem pruning_cycle_pieces_survive :
    pruningNewEdges ⊆ pruningOldEdges ∧
      pruningChord ∈ pruningOldEdges ∧
      pruningChord ∉ pruningNewEdges := by
  decide

end StructuralRamsey.Girth
