import Girth.TrainArbitraryDesignatedOrigin
import Girth.TrainLiteralMixedOrder
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: numerical order for arbitrary geometric long replacements

The generic optional connector block argument needs only two original
VERTEX boundaries at each inserted long piece, not a uniform supreme
label, edge membership in that label, or a strict PlanValid plan.

We use the weak LocalLongBoundaryGeometry contract established for
arbitrary replacement to prove the identical List chain and wrap
conditions. The already verified cyclic kind-word identity then
proves B.twiceOrder = C.twiceOrder for an ACTUAL literal output.

This covers the numerical assertion of the circulation's broad
admissible-replacement lemma, conditional on a legal output BigCycle
and local long geometry; arbitrary A1--A3 and supreme composition
remain separate. No appendix theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The ordered source blocks satisfy the local condition that a fresh
wagon in the NEXT block has two original vertex boundaries. -/
theorem BigCycle.kindBlocks_chain_of_localGeometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces) :
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
      obtain ⟨x, y, hx, hy, _hPx, _hPy⟩ :=
        hGeom j e f p hp
      have hOld : C.connector i = Sum.inl x := by
        rw [← hs] at hx
        rwa [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hx
      exact ⟨by simp [connectorKind, hOld],
        by simp [connectorKind, hy]⟩

/-- At the cyclic first block, the preceding connector is the final
original connector. A long first block has both these boundaries
vertices, exactly as needed to close the numeric cycle. -/
theorem BigCycle.kindBlocks_first_of_localGeometry
    {n : ℕ} (C : D.BigCycle (n + 1))
    (pieces : Fin (n + 1) → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces) :
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
      obtain ⟨x, y, hx, hy, _hPx, _hPy⟩ :=
        hGeom 0 e f p hp
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
theorem BigCycle.kindBlocks_fst_localGeometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    (C.kindBlocks D pieces).map Prod.fst =
      List.ofFn (fun i : Fin n => connectorKind (C.connector i)) := by
  simp [BigCycle.kindBlocks, List.map_ofFn, Function.comp_def]

/-- The generic cyclic connector-kind numeric invariant holds for
every actual strict PlanValid plan, including source length two. -/
theorem BigCycle.kindBlocks_cyclicWeight_of_localGeometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces) :
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
        rw [C.kindBlocks_fst_localGeometry D pieces, List.ofFn_succ']
        simp [enter]
      exact optionalKindWord_cyclicWeight_preserved
        (C.kindBlocks D pieces) enter hLast
        (C.kindBlocks_chain_of_localGeometry D pieces hGeom)
        (C.kindBlocks_first_of_localGeometry D pieces hGeom)

/-- Numerical twice-order is preserved by the ACTUAL literal output
of a mixed PlanValid replacement. This is the missing manuscript
order equality, not merely the previous abstract insertion lemma. -/
theorem BigCycle.literal_resultWord_twiceOrder_of_localGeometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
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
      C.kindBlocks_cyclicWeight_of_localGeometry D pieces hGeom
    _ = cyclicKindTwiceWeight
          (List.ofFn (fun i : Fin n =>
            connectorKind (C.connector i))) := by
      rw [C.kindBlocks_fst_localGeometry D pieces]
    _ = C.twiceOrder := (C.twiceOrder_eq_cyclicKindList D).symm


/-- The full local A2 geometry of an arbitrary long replacement implies
the exact numerical equality of the actual literal expanded cycle.
Neither strict PlanValid nor source acceptability is a premise. -/
theorem BigCycle.literal_resultWord_twiceOrder_of_arbitrary_A2Geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces) :
    B.twiceOrder = C.twiceOrder :=
  C.literal_resultWord_twiceOrder_of_localGeometry D B pieces
    (C.localLongBoundaryGeometry_of_A2 D pieces hGeom) hWord

end StructuralRamsey.Girth.OrderOneData
