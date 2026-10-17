import Girth.TrainPhysicalKindWord
import Girth.TrainSingleShortReplacement
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: numeric order of the actual mixed replacement BigCycle

The literal replacement word has connector blocks [old] or
[fresh wagon, old]. LongValid supplies vertex connectors at both
ends of each inserted block. Thus the source's physical PlanValid
condition supplies the List.IsChain and cyclic first-boundary tests
used by the generic optional-kind numerical lemma.

Combining this with the checked kind-word identity and the equivalence
between cyclic List weight and BigCycle.twiceOrder proves exact numerical
order preservation for an ACTUAL legal literal mixed replacement.

No output A1--A3, wagon linearity, source girth or appendix statement
is used: the only geometry is source PlanValid's LongValid boundary data.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The ordered source blocks satisfy the local condition that a fresh
wagon in the NEXT block has two original vertex boundaries. -/
theorem BigCycle.kindBlocks_chain_of_plan
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    (C.kindBlocks D pieces).IsChain OptionalKindFollow := by
  unfold BigCycle.kindBlocks
  rw [List.isChain_ofFn]
  intro t ht
  let i : Fin n := ⟨t, Nat.lt_of_succ_lt ht⟩
  let j : Fin n := ⟨t + 1, ht⟩
  have hs : cyclicSucc i = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt ht
  change OptionalKindFollow
    (connectorKind (C.connector i), C.pieceIsLong D pieces i)
    (connectorKind (C.connector j), C.pieceIsLong D pieces j)
  intro hFlag
  change C.pieceIsLong D pieces j = true at hFlag
  cases hp : pieces j with
  | keep =>
      simp [BigCycle.pieceIsLong, hp] at hFlag
  | short e =>
      simp [BigCycle.pieceIsLong, hp] at hFlag
  | long e p f =>
      have hLong : C.LongValid D k j e p f :=
        C.longValid_of_piece_eq_long D k j pieces hPlan e f p hp
      obtain ⟨x, y, hx, hy, _he, _hf, _hne, _hpe, _hpf,
        _hxe, _hyf, _hNoPair⟩ := hLong
      have hOld : C.connector i = Sum.inl x := by
        rw [← hs] at hx
        rwa [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hx
      exact ⟨by simp [connectorKind, hOld],
        by simp [connectorKind, hy]⟩

/-- At the cyclic first block, the preceding connector is the final
original connector. A long first block has both these boundaries
vertices, exactly as needed to close the numeric cycle. -/
theorem BigCycle.kindBlocks_first_of_plan
    {n : ℕ} (C : D.BigCycle (n + 1))
    (k : Fin (n + 1))
    (pieces : Fin (n + 1) → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    ∀ a ∈ (C.kindBlocks D pieces).head?,
      OptionalKindFirst
        (connectorKind (C.connector (Fin.last n))) a := by
  intro a ha
  have hHead :
      (C.kindBlocks D pieces).head? =
        some (connectorKind (C.connector 0),
          C.pieceIsLong D pieces 0) := by
    simp [BigCycle.kindBlocks, List.ofFn_succ]
  have hEq :
      (connectorKind (C.connector 0),
        C.pieceIsLong D pieces 0) = a := by
    simpa [hHead] using ha
  subst a
  change C.pieceIsLong D pieces 0 = true →
    connectorKind (C.connector (Fin.last n)) = .vertex ∧
    connectorKind (C.connector 0) = .vertex
  intro hFlag
  cases hp : pieces (0 : Fin (n + 1)) with
  | keep =>
      simp [BigCycle.pieceIsLong, hp] at hFlag
  | short e =>
      simp [BigCycle.pieceIsLong, hp] at hFlag
  | long e p f =>
      have hLong : C.LongValid D k 0 e p f :=
        C.longValid_of_piece_eq_long D k 0 pieces hPlan e f p hp
      obtain ⟨x, y, hx, hy, _he, _hf, _hne, _hpe, _hpf,
        _hxe, _hyf, _hNoPair⟩ := hLong
      have hPred0 :
          trainCyclicPred (0 : Fin (n + 1)) = Fin.last n := by
        apply Fin.ext
        change (0 + (n + 1) - 1) % (n + 1) = n
        have hn : n < n + 1 := by omega
        simp [Nat.mod_eq_of_lt hn]
      rw [hPred0] at hx
      exact ⟨by simp [connectorKind, hx],
        by simp [connectorKind, hy]⟩

/-- Forgetting the Boolean insertion flags in kindBlocks recovers
precisely the old source connector-kind List in source index order. -/
theorem BigCycle.kindBlocks_fst
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    (C.kindBlocks D pieces).map Prod.fst =
      List.ofFn (fun i : Fin n => connectorKind (C.connector i)) := by
  simp [BigCycle.kindBlocks, List.map_ofFn, Function.comp_def]

/-- The generic cyclic connector-kind numeric invariant holds for
every actual strict PlanValid plan, including source length two. -/
theorem BigCycle.kindBlocks_cyclicWeight_preserved
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    cyclicKindTwiceWeight (optionalKindWord (C.kindBlocks D pieces)) =
      cyclicKindTwiceWeight ((C.kindBlocks D pieces).map Prod.fst) := by
  cases n with
  | zero =>
      have hn := C.length_ge_two
      omega
  | succ n' =>
      let enter : CycleConnectorKind :=
        connectorKind (C.connector (Fin.last n'))
      have hLast :
          ((C.kindBlocks D pieces).map Prod.fst).getLast? =
            some enter := by
        rw [C.kindBlocks_fst D pieces, List.ofFn_succ']
        simp [enter]
      exact optionalKindWord_cyclicWeight_preserved
        (C.kindBlocks D pieces) enter hLast
        (C.kindBlocks_chain_of_plan D k pieces hPlan)
        (C.kindBlocks_first_of_plan D k pieces hPlan)

/-- Numerical twice-order is preserved by the ACTUAL literal output
of a mixed PlanValid replacement. This is the missing manuscript
order equality, not merely the previous abstract insertion lemma. -/
theorem BigCycle.literal_resultWord_twiceOrder
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.twiceOrder = C.twiceOrder := by
  have hTypes :
      List.ofFn (fun i : Fin m => connectorKind (B.connector i)) =
        optionalKindWord (C.kindBlocks D pieces) := by
    calc
      List.ofFn (fun i : Fin m => connectorKind (B.connector i)) =
          (List.ofFn (fun i : Fin m =>
            (B.label i, B.connector i))).map
              (fun entry => connectorKind entry.2) := by
            simp [List.map_ofFn, Function.comp_def]
      _ = (C.resultWord D pieces).map
            (fun entry => connectorKind entry.2) :=
          congrArg (List.map (fun entry => connectorKind entry.2)) hWord
      _ = optionalKindWord (C.kindBlocks D pieces) :=
          C.resultWord_kindList D pieces
  calc
    B.twiceOrder =
        cyclicKindTwiceWeight
          (List.ofFn (fun i : Fin m =>
            connectorKind (B.connector i))) :=
      B.twiceOrder_eq_cyclicKindList D
    _ = cyclicKindTwiceWeight
          (optionalKindWord (C.kindBlocks D pieces)) :=
      congrArg cyclicKindTwiceWeight hTypes
    _ = cyclicKindTwiceWeight
          ((C.kindBlocks D pieces).map Prod.fst) :=
      C.kindBlocks_cyclicWeight_preserved D k pieces hPlan
    _ = cyclicKindTwiceWeight
          (List.ofFn (fun i : Fin n =>
            connectorKind (C.connector i))) := by
      rw [C.kindBlocks_fst D pieces]
    _ = C.twiceOrder := (C.twiceOrder_eq_cyclicKindList D).symm

end StructuralRamsey.Girth.OrderOneData
