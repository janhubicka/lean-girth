import Girth.TrainArbitraryBoundaryLabels
import Girth.TrainPlanCyclicWrap
import Girth.TrainArbitraryConnectorNodup
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-!
# Circulation: arbitrary local pieces produce a genuine BigCycle at length >=3

For a source acceptable cycle of length at least three, an arbitrary
simultaneous choice of locally incident short and long pieces needs
no selected supreme label. Fresh long wagons with the correct physical
old vertex contacts are automatically pairwise distinct by A3.

The checked local piece chains, source boundary label inequalities,
and universal last-to-first flattening lemma now verify every field
of CyclicWordChecks for the ACTUAL flattened replacement word. Hence
the word represents a genuine BigCycle.

This is the final automatic LEGALITY assertion in the circulated
admissible-replacement lemma. The later supreme composition is
independent. No appendix input or output acceptability assumption.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Adjacent arbitrary replacement block endpoints satisfy the
full label inequality and both physical incidence conditions. -/
theorem BigCycle.arbitrary_boundaryFollow
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (i : Fin n) :
    ∀ᵉ (a ∈ (C.pieceWord D i (pieces i)).getLast?)
      (b ∈ (C.pieceWord D (cyclicSucc i)
        (pieces (cyclicSucc i))).head?),
      D.CyclicPairFollow a b := by
  have hLast := C.pieceWord_getLast?_eq D i (pieces i)
  obtain ⟨conn, hHead⟩ :=
    C.pieceWord_head?_first D (cyclicSucc i) (pieces (cyclicSucc i))
  have hDifferent :=
    C.arbitrary_adjacent_piece_labels_ne
      D hAccept hn pieces hInc hGeom hFresh i
  have hLastInc :=
    C.pieceLast_incident_of_localIncidence D pieces hInc i
  have hFirstInc :=
    C.pieceFirst_incident_of_localIncidence
      D pieces hInc (cyclicSucc i)
  rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i]
    at hFirstInc
  have hRel : D.CyclicPairFollow
      (C.pieceLastLabel D (C.label i) (pieces i), C.connector i)
      (C.pieceFirstLabel D (C.label (cyclicSucc i))
        (pieces (cyclicSucc i)), conn) :=
    ⟨hDifferent, hLastInc, hFirstInc⟩
  simpa [hLast, hHead] using hRel

/-- The ordinary source-indexed list of replacement blocks is
a chain, with the cyclic closing boundary treated separately. -/
theorem BigCycle.arbitrary_pieceBlocks_isChain
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    (List.ofFn (fun i : Fin n => C.pieceWord D i (pieces i))).IsChain
      (fun a b => ∀ᵉ (x ∈ a.getLast?) (y ∈ b.head?),
        D.CyclicPairFollow x y) := by
  rw [List.isChain_ofFn]
  intro i hi
  let j : Fin n := ⟨i, Nat.lt_of_succ_lt hi⟩
  have hNext : cyclicSucc j = ⟨i + 1, hi⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  simpa [j, hNext] using
    C.arbitrary_boundaryFollow
      D hAccept hn pieces hInc hGeom hFresh j

/-- The physical last-to-first boundary relation is exactly the
cyclic source boundary at its last original occurrence. -/
theorem BigCycle.arbitrary_last_first_source_boundary
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
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
    have hh : n - 1 + 1 = n := by omega
    rw [hh, Nat.mod_self]
  have h := C.arbitrary_boundaryFollow
    D hAccept hn pieces hInc hGeom hFresh last
  simpa [last, hs] using h

/-- The source last-to-first block relation is the wrap of the
actual concatenated word; this uses no selected source target. -/
theorem BigCycle.arbitrary_resultWord_wrap
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    D.CyclicPairFollow
      ((C.resultWord D pieces).get
        ⟨(C.resultWord D pieces).length - 1, by
          have hh := C.resultWord_length_ge_source D pieces
          omega⟩)
      ((C.resultWord D pieces).get
        ⟨0, by
          have hh := C.resultWord_length_ge_source D pieces
          omega⟩) := by
  let blocks := List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))
  have hBlocks : blocks ≠ [] := by simp [blocks]; omega
  have hFirstEq : blocks.head hBlocks =
      C.pieceWord D ⟨0, by omega⟩ (pieces ⟨0, by omega⟩) :=
    C.blockList_head_eq_first D (by omega) pieces
  have hLastEq : blocks.getLast hBlocks =
      C.pieceWord D ⟨n-1, by omega⟩ (pieces ⟨n-1, by omega⟩) :=
    C.blockList_getLast_eq_last D (by omega) pieces
  have hFirstNe : blocks.head hBlocks ≠ [] := by
    rw [hFirstEq]
    exact C.pieceWord_ne_nil D _ _
  have hLastNe : blocks.getLast hBlocks ≠ [] := by
    rw [hLastEq]
    exact C.pieceWord_ne_nil D _ _
  have hSource :=
    C.arbitrary_last_first_source_boundary
      D hAccept hn pieces hInc hGeom hFresh
  have hBlocksWrap :
      ∀ᵉ (a ∈ (blocks.getLast hBlocks).getLast?)
          (b ∈ (blocks.head hBlocks).head?),
        D.CyclicPairFollow a b := by
    simpa [hFirstEq, hLastEq, blocks] using hSource
  have hFlat := flatten_wrap_of_nonempty_blocks
    D.CyclicPairFollow blocks hBlocks hFirstNe hLastNe hBlocksWrap
  simpa [BigCycle.resultWord, blocks] using hFlat

/-- COMPLETE global legality of the literal arbitrary simultaneous
replacement word at source length at least three, with no selected
supreme label: it is the word of an actual BigCycle. -/
theorem BigCycle.arbitrary_planProducesBigCycle_of_localGeometry
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    C.PlanProducesBigCycle D pieces := by
  let blocks :=
    List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))
  have hNonempty : ([] : List ((I ⊕ E) × (V ⊕ P))) ∉ blocks := by
    intro hh
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hh
    exact (C.pieceWord_ne_nil D j (pieces j)) hj
  have hLength : 2 ≤ blocks.flatten.length := by
    have hh := C.resultWord_length_ge_source D pieces
    simpa [BigCycle.resultWord, blocks] using le_trans (by omega : 2 ≤ n) hh
  have hNodup : (blocks.flatten.map Prod.snd).Nodup := by
    simpa [blocks, BigCycle.resultWord] using
      C.arbitrary_resultWord_connectors_nodup
        D hAccept hn pieces
        (C.localLongBoundaryGeometry_of_A2 D pieces hGeom) hFresh
  have hInside : ∀ block ∈ blocks, block.IsChain D.CyclicPairFollow := by
    intro block hb
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hb
    subst block
    exact C.pieceWord_isChain_of_localIncidence D pieces hInc j
  have hBoundary :=
    C.arbitrary_pieceBlocks_isChain
      D hAccept hn pieces hInc hGeom hFresh
  have hWrap :=
    C.arbitrary_resultWord_wrap
      D hAccept hn pieces hInc hGeom hFresh
  have hCheck : D.CyclicWordChecks blocks.flatten :=
    D.cyclicWordChecks_of_flattened_blocks blocks
      hNonempty hLength hNodup hInside hBoundary
      (by simpa [blocks, BigCycle.resultWord] using hWrap)
  exact (C.planProducesBigCycle_iff_wordChecks D pieces).mpr
    (by simpa [blocks, BigCycle.resultWord] using hCheck)

end StructuralRamsey.Girth.OrderOneData
