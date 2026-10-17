import Girth.TrainCycleSegmentWeight
import Mathlib.Tactic

/-!
# Circulation: numerical order of optional wagon insertions

The connector-kind word of a literal replacement plan consists of blocks
[old] or [wagon, old]. A fresh wagon can be inserted only when both
the preceding and current original connectors are vertices.

The local equality 2 = 1 + 1 then proves that the twice-weight of the
entire expanded walk, with the same entering connector, is unchanged.
Unlike abstract one-step insertion, this is a reusable simultaneous
block-list theorem. The separate remaining task is identifying the
cyclic List/ofFn twice-weight with the manuscript's BigCycle.twiceOrder.

No output acceptability, physical wagon linearity, or appendix claim
is used by this purely numerical lemma.
-/

namespace StructuralRamsey.Girth

/-- Each old connector is either retained alone or preceded by one
inserted wagon; the Bool records whether insertion takes place. -/
def optionalKindWord : List (CycleConnectorKind × Bool) → List CycleConnectorKind
  | [] => []
  | (kind, false) :: rest => kind :: optionalKindWord rest
  | (kind, true) :: rest => .wagon :: kind :: optionalKindWord rest

/-- The exact vertex-boundary condition for a sequence of optional
wagon insertions, starting with the specified entering connector. -/
def OptionalKindValid (enter : CycleConnectorKind) :
    List (CycleConnectorKind × Bool) → Prop
  | [] => True
  | (kind, false) :: rest => OptionalKindValid kind rest
  | (kind, true) :: rest =>
      enter = .vertex ∧ kind = .vertex ∧ OptionalKindValid kind rest

/-- Optional fresh wagons preserve the twice-weight of the literal
expanded walk, not merely of a single replacement. The entering
connector is held fixed and the final old connector is retained. -/
theorem OptionalKindValid.twiceSegmentWeight_preserved
    (enter : CycleConnectorKind)
    (blocks : List (CycleConnectorKind × Bool))
    (h : OptionalKindValid enter blocks) :
    twiceSegmentWeight enter (optionalKindWord blocks) =
      twiceSegmentWeight enter (blocks.map Prod.fst) := by
  induction blocks generalizing enter with
  | nil =>
      rfl
  | cons hd rest ih =>
      rcases hd with ⟨kind, inserted⟩
      cases inserted with
      | false =>
          have hRest : OptionalKindValid kind rest := by
            simpa [OptionalKindValid] using h
          simpa [optionalKindWord, twiceSegmentWeight] using
            congrArg (fun x : ℕ =>
              twiceOccurrenceWeight enter kind + x) (ih kind hRest)
      | true =>
          have hValid :
              enter = .vertex ∧ kind = .vertex ∧
                OptionalKindValid kind rest := by
            simpa [OptionalKindValid] using h
          rcases hValid with ⟨hEnter, hKind, hRest⟩
          subst enter
          subst kind
          have hTail := ih CycleConnectorKind.vertex hRest
          simpa [optionalKindWord, twiceSegmentWeight,
            twiceOccurrenceWeight] using
              congrArg (fun x : ℕ => 2 + x) hTail

end StructuralRamsey.Girth
