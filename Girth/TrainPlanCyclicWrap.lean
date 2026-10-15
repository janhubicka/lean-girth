import Girth.TrainPlanGlobalAssembly
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
Circulation: transport the last-to-first source boundary through the
literal flattened list of replacement pieces.

This is the final finite-word step after checked connector Nodup,
local piece chains, and the global chain of consecutive blocks. A
valid fresh mixed short/long supreme plan then really produces the
BigCycle demanded by the original circulation definition.

The result is about BigCycle LEGALITY, not yet about the new cycle's
A1--A3 acceptability or composition of supreme replacements.
-/

namespace StructuralRamsey.Girth

universe v

/-- A cyclic relation on the last entry of the last nonempty block
and first entry of the first nonempty block is exactly the relation
on the last and first entries of the flattened list. -/
private theorem flatten_wrap_of_nonempty_blocks
    {α : Type v} (R : α → α → Prop)
    (blocks : List (List α))
    (hBlocks : blocks ≠ [])
    (hFirst : blocks.head hBlocks ≠ [])
    (hLast : blocks.getLast hBlocks ≠ [])
    (hWrap : ∀ᵉ (a ∈ (blocks.getLast hBlocks).getLast?)
                (b ∈ (blocks.head hBlocks).head?), R a b) :
    R
      (blocks.flatten.get
        ⟨blocks.flatten.length - 1, by
          have hf := List.flatten_ne_nil_iff.mpr
            ⟨blocks.head hBlocks, List.head_mem hBlocks, hFirst⟩
          have hp := List.length_pos_of_ne_nil hf
          omega⟩)
      (blocks.flatten.get
        ⟨0, by
          have hf := List.flatten_ne_nil_iff.mpr
            ⟨blocks.head hBlocks, List.head_mem hBlocks, hFirst⟩
          exact List.length_pos_of_ne_nil hf⟩) := by
  have hFlat : blocks.flatten ≠ [] :=
    List.flatten_ne_nil_iff.mpr
      ⟨blocks.head hBlocks, List.head_mem hBlocks, hFirst⟩
  have hHeadOpt : (blocks.head hBlocks).head? =
      some ((blocks.head hBlocks).head hFirst) := by
    cases hh : blocks.head hBlocks with
    | nil => exact False.elim (hFirst hh)
    | cons a as => rfl
  have hLastOpt : (blocks.getLast hBlocks).getLast? =
      some ((blocks.getLast hBlocks).getLast hLast) :=
    List.getLast?_eq_getLast_of_ne_nil hLast
  have hR : R
      ((blocks.getLast hBlocks).getLast hLast)
      ((blocks.head hBlocks).head hFirst) := by
    simpa [hHeadOpt, hLastOpt] using hWrap
  have hTailEq := List.getLast_flatten_eq_getLast_getLast
    (hl := hFlat) (hl' := hLast)
  have hHeadEq := List.head_flatten_eq_head_head
    (hl := hFlat) (hl' := hFirst)
  have hIndexLast :=
    List.get_length_sub_one (l := blocks.flatten)
      (h := by have hp := List.length_pos_of_ne_nil hFlat; omega)
  have hIndexFirst := List.head_eq_getElem_zero (hl := hFlat)
  simpa [hIndexLast, hIndexFirst, hTailEq, hHeadEq] using hR

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The first selected block is literally the replacement at old position 0. -/
private theorem BigCycle.blockList_head_eq_first
    {n : ℕ} (C : D.BigCycle n)
    (hn : 0 < n) (pieces : Fin n → TrainSupremePiece E P) :
    (List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))).head
      (by simp; omega) =
    C.pieceWord D ⟨0, hn⟩ (pieces ⟨0, hn⟩) := by
  cases n with
  | zero => omega
  | succ m =>
      simp [List.head_ofFn]

/-- The last selected block is literally the replacement at old n-1. -/
private theorem BigCycle.blockList_getLast_eq_last
    {n : ℕ} (C : D.BigCycle n)
    (hn : 0 < n) (pieces : Fin n → TrainSupremePiece E P) :
    (List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))).getLast
      (by simp; omega) =
    C.pieceWord D ⟨n-1, by omega⟩
      (pieces ⟨n-1, by omega⟩) := by
  cases n with
  | zero => omega
  | succ m =>
      simpa [Fin.last] using
        (List.getLast_ofFn_succ
          (f := fun j : Fin (m + 1) => C.pieceWord D j (pieces j)))

/-- The genuine final-to-first connector relation of the flattened word
is inherited from the old final-to-first replacement boundary. -/
theorem BigCycle.resultWord_wrap_of_plan
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    D.CyclicPairFollow
      ((C.resultWord D pieces).get
        ⟨(C.resultWord D pieces).length - 1, by
          have hl := C.resultWord_length_ge_source D pieces
          omega⟩)
      ((C.resultWord D pieces).get
        ⟨0, by
          have hl := C.resultWord_length_ge_source D pieces
          omega⟩) := by
  let blocks := List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))
  have hBlocks : blocks ≠ [] := by simp [blocks]; omega
  have hFirstEq : blocks.head hBlocks =
      C.pieceWord D ⟨0, by omega⟩ (pieces ⟨0, by omega⟩) := by
    exact C.blockList_head_eq_first D (by omega) pieces
  have hLastEq : blocks.getLast hBlocks =
      C.pieceWord D ⟨n-1, by omega⟩ (pieces ⟨n-1, by omega⟩) := by
    exact C.blockList_getLast_eq_last D (by omega) pieces
  have hFirstNe : blocks.head hBlocks ≠ [] := by
    rw [hFirstEq]
    exact C.pieceWord_ne_nil D _ _
  have hLastNe : blocks.getLast hBlocks ≠ [] := by
    rw [hLastEq]
    exact C.pieceWord_ne_nil D _ _
  have hSource := C.plan_last_first_source_boundary D
    hAccept hn k hk pieces hPlan hFresh
  have hBlocksWrap :
      ∀ᵉ (a ∈ (blocks.getLast hBlocks).getLast?)
          (b ∈ (blocks.head hBlocks).head?), D.CyclicPairFollow a b := by
    simpa [hFirstEq, hLastEq, blocks] using hSource
  have hFlattenWrap := flatten_wrap_of_nonempty_blocks
    D.CyclicPairFollow blocks hBlocks hFirstNe hLastNe hBlocksWrap
  simpa [BigCycle.resultWord, blocks] using hFlattenWrap

/-- FULL literal global BigCycle assembly for a valid fresh mixed
short/long supreme plan, at every source length at least three.
This removes the previous last-to-first wrap assumption. -/
theorem BigCycle.planProducesBigCycle_of_fresh_long
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.PlanProducesBigCycle D pieces :=
  C.planProducesBigCycle_of_wrap D hAccept hn k hk pieces hPlan hFresh
    (C.resultWord_wrap_of_plan D hAccept hn k hk pieces hPlan hFresh)

end OrderOneData
end StructuralRamsey.Girth
