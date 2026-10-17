import Girth.TrainFinCyclicOrder
import Girth.TrainInsertedConnectorNodup
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: literal replacement connector kinds are optional blocks

A short or retained source occurrence contributes its old connector.
A long piece contributes a fresh wagon connector followed by that
same old connector. After taking connector kinds, the actual physical
resultWord therefore equals the generic optionalKindWord of the
old connector kinds and a Boolean insertion mask.

This identity is about the *ordered literal List*, not merely a set
of connectors, and is independent of output A1--A3, wagon linearity,
girth and the appendix.
-/

namespace StructuralRamsey.Girth

/-- The generic one- or two-entry block of a Boolean insertion mask. -/
def kindBlockFromPair : CycleConnectorKind × Bool →
    List CycleConnectorKind
  | (old, false) => [old]
  | (old, true) => [.wagon, old]

/-- The recursive optionalKindWord is exactly the flattened sequence
of its individual insertion blocks. -/
theorem optionalKindWord_eq_flatten
    (blocks : List (CycleConnectorKind × Bool)) :
    optionalKindWord blocks =
      (blocks.map kindBlockFromPair).flatten := by
  induction blocks with
  | nil => rfl
  | cons hd tail ih =>
      rcases hd with ⟨old, insert⟩
      cases insert <;>
        simp [optionalKindWord, kindBlockFromPair, ih]

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Indicator of a genuine long replacement piece at a source index. -/
def BigCycle.pieceIsLong
    {n : ℕ} (_C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) (i : Fin n) : Bool :=
  match pieces i with
  | .long _ _ _ => true
  | .keep => false
  | .short _ => false

/-- Exact block data for computing numeric weight from the source
cyclic connector list. -/
def BigCycle.kindBlocks
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    List (CycleConnectorKind × Bool) :=
  List.ofFn (fun i : Fin n =>
    (connectorKind (C.connector i), C.pieceIsLong D pieces i))

/-- Taking connector kinds of the literal mixed replacement word
commutes with expansion into optional fresh-wagon blocks. -/
theorem BigCycle.resultWord_kindList
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    (C.resultWord D pieces).map
      (fun e => connectorKind e.2) =
      optionalKindWord (C.kindBlocks D pieces) := by
  classical
  unfold BigCycle.resultWord BigCycle.kindBlocks
  rw [List.map_flatten, ← List.ofFn_comp']
  rw [optionalKindWord_eq_flatten, ← List.ofFn_comp']
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  cases hp : pieces i with
  | keep =>
      simp [BigCycle.pieceWord, BigCycle.pieceIsLong,
        kindBlockFromPair, hp]
  | short e =>
      simp [BigCycle.pieceWord, BigCycle.pieceIsLong,
        kindBlockFromPair, hp]
  | long e p f =>
      simp [BigCycle.pieceWord, BigCycle.pieceIsLong,
        kindBlockFromPair, connectorKind, hp]

end OrderOneData
end StructuralRamsey.Girth
