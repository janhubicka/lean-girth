import Girth.TrainCheckedCycleWord
import Girth.TrainLongBoundaryCollision
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Circulation: reduce an expanded cyclic word to ordinary list chains

The checked-word interface from the fully verified #522 uses five tests
on the final list of label/connector pairs. Instead of separately
reindexing all inserted long-piece positions, one may check an ordinary
linear chain relation on the flattened list, plus its last-to-first wrap.

The chain relation at successive word entries contains exactly the
adjacent-label inequality and both physical incidences with the earlier
connector. Pairwise distinct connector entries provide injectivity.

Mathlib's isChain_flatten then reduces chain legality of an actual
list of replacement blocks to legality inside each block and at
each block boundary. The new results never assume an output BigCycle
or output wagon linearity, and prove neither the geometric block
conditions nor source-to-output A2/A3 transfer.

This is a generic, reusable finite-word assembly interface, entirely
within the circulation proof.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

-- A word entry is its occurrence label followed by its right connector.
private abbrev Entry := (I ⊕ E) × (V ⊕ P)

/-- Exactly the three checks involving a consecutive pair of word entries:
different labels and incidence of both labels with the first connector. -/
def CyclicPairFollow (a b : Entry (V := V) (E := E) (I := I) (P := P)) : Prop :=
  a.1 ≠ b.1 ∧ D.Incident a.1 a.2 ∧ D.Incident b.1 a.2

/-- The ordinary (non-cyclic) list chain together with the final wrap
controls every adjacent pair in a cyclic word, including its last-to-first
pair, without introducing a second expanded Fin indexing scheme. -/
theorem cyclicPairFollow_all_of_chain_wrap
    (word : List (Entry (V := V) (E := E) (I := I) (P := P)))
    (hLength : 2 ≤ word.length)
    (hChain : word.IsChain D.CyclicPairFollow)
    (hWrap : D.CyclicPairFollow
      (word.get ⟨word.length - 1, by omega⟩)
      (word.get ⟨0, by omega⟩)) :
    ∀ i : Fin word.length,
      D.CyclicPairFollow (word.get i)
        (word.get (cyclicSucc i)) := by
  intro i
  by_cases hi : i.val + 1 < word.length
  · have hc := (List.isChain_iff_getElem.mp hChain) i.val hi
    have hs : cyclicSucc i = ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hi
    simpa [hs] using hc
  · have heq : i.val = word.length - 1 := by omega
    have hz : cyclicSucc i = ⟨0, by omega⟩ := by
      apply Fin.ext
      change (i.val + 1) % word.length = 0
      have hsum : i.val + 1 = word.length := by omega
      rw [hsum, Nat.mod_self]
    have hlast : i = ⟨word.length - 1, by omega⟩ :=
      Fin.ext heq
    rw [hz, hlast]
    exact hWrap

/-- From connector Nodup and a chain with cyclic wrap, construct the
five EXACT tests needed to build the literal output BigCycle. -/
theorem cyclicWordChecks_of_chain_wrap
    (word : List (Entry (V := V) (E := E) (I := I) (P := P)))
    (hLength : 2 ≤ word.length)
    (hNodup : (word.map Prod.snd).Nodup)
    (hChain : word.IsChain D.CyclicPairFollow)
    (hWrap : D.CyclicPairFollow
      (word.get ⟨word.length - 1, by omega⟩)
      (word.get ⟨0, by omega⟩)) :
    D.CyclicWordChecks word := by
  have hFollow := D.cyclicPairFollow_all_of_chain_wrap
    word hLength hChain hWrap
  refine ⟨hLength, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hn := List.nodup_iff_injective_get.mp hNodup
    have heq : (word.map Prod.snd).get
        ⟨i.val, by simpa using i.isLt⟩ =
      (word.map Prod.snd).get
        ⟨j.val, by simpa using j.isLt⟩ := by
      simpa using hij
    apply Fin.ext
    exact congrArg
      (fun t : Fin (word.map Prod.snd).length => t.val) (hn heq)
  · intro i
    exact (hFollow i).1
  · intro i
    exact (hFollow i).2.1
  · intro i
    exact (hFollow i).2.2

/-- The actual flattened list of replacement blocks is a legal cyclic
word whenever each block is internally a chain, consecutive blocks
respect the boundary relation, the wrap is legal, and connectors are
distinct. This is the Mathlib chain-flatten bridge. -/
theorem cyclicWordChecks_of_flattened_blocks
    (blocks : List (List (Entry (V := V) (E := E) (I := I) (P := P))))
    (hNonempty : [] ∉ blocks)
    (hLength : 2 ≤ blocks.flatten.length)
    (hNodup : (blocks.flatten.map Prod.snd).Nodup)
    (hInside : ∀ b ∈ blocks, b.IsChain D.CyclicPairFollow)
    (hBoundary : blocks.IsChain (fun b c =>
      ∀ᵉ (x ∈ b.getLast?) (y ∈ c.head?), D.CyclicPairFollow x y))
    (hWrap : D.CyclicPairFollow
      (blocks.flatten.get ⟨blocks.flatten.length - 1, by omega⟩)
      (blocks.flatten.get ⟨0, by omega⟩)) :
    D.CyclicWordChecks blocks.flatten := by
  apply D.cyclicWordChecks_of_chain_wrap blocks.flatten
    hLength hNodup
  · exact (List.isChain_flatten hNonempty).mpr ⟨hInside, hBoundary⟩
  · exact hWrap


/-- Every replacement piece produces at least one physical occurrence. -/
theorem BigCycle.pieceWord_ne_nil
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (piece : TrainSupremePiece E P) :
    C.pieceWord D j piece ≠ [] := by
  cases piece <;> simp [BigCycle.pieceWord]

/-- The local PlanValid conditions make each physical replacement piece a
chain on the actual occurrence/connector word. Long pieces use their two
distinct edges and common parent wagon; short and retained pieces are
singletons. No global BigCycle witness is used. -/
theorem BigCycle.pieceWord_isChain_of_plan
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) (j : Fin n) :
    (C.pieceWord D j (pieces j)).IsChain D.CyclicPairFollow := by
  classical
  cases hp : pieces j with
  | keep =>
      simp [BigCycle.pieceWord, hp]
  | short e =>
      simp [BigCycle.pieceWord, hp]
  | long e w f =>
      have hv : C.LongValid D k j e w f :=
        C.longValid_of_piece_eq_long D k j pieces hPlan e f w hp
      obtain ⟨x, y, hx, hy, he, hf, hne, hpe, hpf, hxe, hyf, hno⟩ := hv
      change ([(Sum.inr e, Sum.inr w),
        (Sum.inr f, C.connector j)]).IsChain D.CyclicPairFollow
      apply List.isChain_pair.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro h
        exact hne (Sum.inr.inj h)
      · exact ⟨e, rfl, hpe⟩
      · exact ⟨f, rfl, hpf⟩

/-- The LAST label in any valid piece is incident with the ORIGINAL right
connector of that occurrence. -/
theorem BigCycle.pieceLast_incident_of_plan
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) (j : Fin n) :
    D.Incident
      (C.pieceLastLabel D (C.label j) (pieces j))
      (C.connector j) := by
  classical
  cases hp : pieces j with
  | keep =>
      simpa [BigCycle.pieceLastLabel, hp] using C.left_incident j
  | short e =>
      have hv : C.ShortValid D k j e :=
        C.shortValid_of_piece_eq_short D k j pieces hPlan e hp
      simpa [BigCycle.pieceLastLabel, hp] using hv.2.2
  | long e w f =>
      have hv : C.LongValid D k j e w f :=
        C.longValid_of_piece_eq_long D k j pieces hPlan e f w hp
      obtain ⟨x, y, hx, hy, he, hf, hne, hpe, hpf, hxe, hyf, hno⟩ := hv
      simp only [BigCycle.pieceLastLabel, hp]
      rw [hy]
      exact hyf

/-- The FIRST label in any valid piece is incident with the ORIGINAL
preceding connector; it is a real local edge probe in short/long pieces,
or the unchanged source incidence in a kept occurrence. -/
theorem BigCycle.pieceFirst_incident_of_plan
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) (j : Fin n) :
    D.Incident
      (C.pieceFirstLabel D (C.label j) (pieces j))
      (C.connector (trainCyclicPred j)) := by
  classical
  cases hp : pieces j with
  | keep =>
      have h := C.right_incident (trainCyclicPred j)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two j] at h
      simpa [BigCycle.pieceFirstLabel, hp] using h
  | short e =>
      have hv : C.ShortValid D k j e :=
        C.shortValid_of_piece_eq_short D k j pieces hPlan e hp
      simpa [BigCycle.pieceFirstLabel, hp] using hv.2.1
  | long e w f =>
      have hv : C.LongValid D k j e w f :=
        C.longValid_of_piece_eq_long D k j pieces hPlan e f w hp
      obtain ⟨x, y, hx, hy, he, hf, hne, hpe, hpf, hxe, hyf, hno⟩ := hv
      simp only [BigCycle.pieceFirstLabel, hp]
      rw [hx]
      exact hxe

end StructuralRamsey.Girth.OrderOneData
