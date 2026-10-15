import Girth.TrainExpandedWordChain
import Girth.TrainInsertedConnectorNodup
import Mathlib.Data.List.ChainOfFn

/-!
# Circulation: assemble the ordinary chain of actual replacement blocks

For a valid supreme plan, the first/last physical labels of each
replacement block have precisely the ORIGINAL connector incidences.
The checked #520 boundary inequality supplies the remaining relation
between the last label of block i and the first of block succ(i).

Mathlib's List.isChain_ofFn turns these local relations into an
ordinary chain on the list of real piece words. The only cyclic
condition still to add is the last-to-first wraparound.

No output BigCycle, output-wagon linearity or A1--A3 transfer is
assumed in this module.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The final physical entry of a piece has its last label and exactly
the old right connector of that occurrence. -/
theorem BigCycle.pieceWord_getLast?_eq
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (piece : TrainSupremePiece E P) :
    (C.pieceWord D j piece).getLast? =
      some (C.pieceLastLabel D (C.label j) piece, C.connector j) := by
  cases piece <;> rfl

/-- The first physical entry of a piece has its first label; its
connector may be new when the piece is long. -/
theorem BigCycle.pieceWord_head?_first
    {n : ℕ} (C : D.BigCycle n) (j : Fin n)
    (piece : TrainSupremePiece E P) :
    ∃ connector : V ⊕ P,
      (C.pieceWord D j piece).head? =
        some (C.pieceFirstLabel D (C.label j) piece, connector) := by
  cases piece with
  | keep => exact ⟨C.connector j, rfl⟩
  | short e => exact ⟨C.connector j, rfl⟩
  | long e w f => exact ⟨Sum.inr w, rfl⟩

/-- All original neighbouring replacement blocks satisfy exactly the
label inequality and physical incidences needed at their interface. -/
theorem BigCycle.boundaryFollow_of_plan
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
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
    C.plan_adjacent_piece_labels_ne D hAccept hn k hk pieces hPlan hFresh i
  have hLastInc :=
    C.pieceLast_incident_of_plan D k pieces hPlan i
  have hFirstInc :=
    C.pieceFirst_incident_of_plan D k pieces hPlan (cyclicSucc i)
  rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i] at hFirstInc
  have hRel : D.CyclicPairFollow
      (C.pieceLastLabel D (C.label i) (pieces i), C.connector i)
      (C.pieceFirstLabel D (C.label (cyclicSucc i))
        (pieces (cyclicSucc i)), conn) :=
    ⟨hDifferent, hLastInc, hFirstInc⟩
  simpa [hLast, hHead] using hRel

/-- The genuine sequence of replacement blocks is an ordinary chain.
This includes every INTERNAL boundary between consecutive original
occurrences, but deliberately leaves final-to-first wrap separate. -/
theorem BigCycle.pieceBlocks_isChain_of_plan
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n) (hk : D.designated (C.label k))
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (j : Fin n) (e : E) (p : P) (f : E),
      pieces j = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) :
    (List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j))).IsChain
      (fun a b => ∀ᵉ (x ∈ a.getLast?) (y ∈ b.head?),
        D.CyclicPairFollow x y) := by
  rw [List.isChain_ofFn]
  intro i hi
  let j : Fin n := ⟨i, Nat.lt_of_succ_lt hi⟩
  have hNext : cyclicSucc j = ⟨i + 1, hi⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  simpa [j, hNext] using
    C.boundaryFollow_of_plan D hAccept hn k hk pieces hPlan hFresh j

/-- Every selected piece block is nonempty and itself a physical
chain, precisely as required by the checked List.isChain_flatten
interface. -/
theorem BigCycle.pieceBlocks_nonempty_and_inside
    {n : ℕ} (C : D.BigCycle n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces) :
    ([] : List ((I ⊕ E) × (V ⊕ P))) ∉
      List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j)) ∧
      (∀ block ∈
        List.ofFn (fun j : Fin n => C.pieceWord D j (pieces j)),
        block.IsChain D.CyclicPairFollow) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    exact (C.pieceWord_ne_nil D j (pieces j)) hj
  · intro block hb
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hb
    subst block
    exact C.pieceWord_isChain_of_plan D k pieces hPlan j

end StructuralRamsey.Girth.OrderOneData
