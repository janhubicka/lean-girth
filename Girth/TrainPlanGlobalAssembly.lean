import Girth.TrainPlanBlockChain
import Girth.TrainInsertedConnectorNodup
import Mathlib.Tactic

/-!
Circulation: finish every literal expanded-word check except cyclic wrap.

Each selected piece word has length one or two. The checked PlanValid
block-chain and connector Nodup interfaces then supply all internal and
between-block tests. The remaining input is solely the actual
last-to-first cyclic boundary relation. We deliberately do not assume
an output BigCycle or output wagon linearity.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every occurrence contributes at least one label to the actual
flattened replacement word. -/
theorem BigCycle.resultWord_length_ge_source
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) :
    n ≤ (C.resultWord D pieces).length := by
  classical
  have h : (∑ i : Fin n, (1 : ℕ)) ≤
      ∑ i : Fin n, (C.pieceWord D i (pieces i)).length := by
    apply Finset.sum_le_sum
    intro i _
    cases hp : pieces i with
    | keep => simp [BigCycle.pieceWord]
    | short e => simp [BigCycle.pieceWord]
    | long e p f => simp [BigCycle.pieceWord]
  simpa [BigCycle.resultWord, List.length_flatten,
    List.sum_ofFn, List.map_ofFn] using h

/-- The final-to-first boundary between ORIGINAL replacement blocks
is already an instance of the uniform PlanValid boundary theorem.
Only transport from these literal block endpoints to the flattened
word remains to be checked. -/
theorem BigCycle.plan_last_first_source_boundary
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    ∀ᵉ (a ∈ (C.pieceWord D ⟨n-1, by omega⟩
      (pieces ⟨n-1, by omega⟩)).getLast?)
      (b ∈ (C.pieceWord D ⟨0, by omega⟩
      (pieces ⟨0, by omega⟩)).head?),
      D.CyclicPairFollow a b := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hs : cyclicSucc last = ⟨0, by omega⟩ := by
    apply Fin.ext
    change (n - 1 + 1) % n = 0
    have h : n - 1 + 1 = n := by omega
    rw [h, Nat.mod_self]
  have hb := C.boundaryFollow_of_plan D hAccept hn
    k hk pieces hPlan hFresh last
  simpa [last, hs] using hb

/-- Global legality of a mixed short/long plan is reduced to the one
remaining last-to-first boundary relation on the ACTUAL output word.
All other BigCycle checks are constructed from earlier proven lemmas. -/
theorem BigCycle.planProducesBigCycle_of_wrap
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWrap : D.CyclicPairFollow
      ((C.resultWord D pieces).get
        ⟨(C.resultWord D pieces).length - 1, by
          have h := C.resultWord_length_ge_source D pieces
          omega⟩)
      ((C.resultWord D pieces).get
        ⟨0, by
          have h := C.resultWord_length_ge_source D pieces
          omega⟩)) :
    C.PlanProducesBigCycle D pieces := by
  let blocks :=
    List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))
  have hs := C.pieceBlocks_nonempty_and_inside D k pieces hPlan
  have hb := C.pieceBlocks_isChain_of_plan D
    hAccept hn k hk pieces hPlan hFresh
  have hlen : 2 ≤ blocks.flatten.length := by
    have h := C.resultWord_length_ge_source D pieces
    have hh : 2 ≤ (C.resultWord D pieces).length := le_trans (by omega) h
    simpa only [BigCycle.resultWord] using hh
  have hnodup : (blocks.flatten.map Prod.snd).Nodup := by
    simpa [blocks, BigCycle.resultWord] using
      C.resultWord_connectors_nodup D hAccept hn k pieces hPlan hFresh
  have hchecks : D.CyclicWordChecks blocks.flatten :=
    D.cyclicWordChecks_of_flattened_blocks blocks
      hs.1 hlen hnodup hs.2 hb
      (by simpa [blocks, BigCycle.resultWord] using hWrap)
  exact (C.planProducesBigCycle_iff_wordChecks D pieces).mpr
    (by simpa [blocks, BigCycle.resultWord] using hchecks)

end StructuralRamsey.Girth.OrderOneData
