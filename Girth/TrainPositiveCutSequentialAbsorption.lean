import Girth.TrainSingleShortReplacement
import Girth.TrainArbitrarySupremeComposition
import Girth.TrainShortOnlyPlanGlobal

/-!
# Track A: successive physical short absorptions preserve supremeness

Minimum-segmentation arguments may move a SINGLE short/singleton
segment at a time. It is generally unjustified to assume that all
foreign labels can be replaced in ONE simultaneous move into a
chosen standard: an internal vertex of a foreign block need not
belong to that standard.

The one-step theorem identifies the actual relabelled BigCycle with
an arbitrary literal short replacement word and pulls indexed
supremeness back by the already checked composition theorem.
The finite-chain theorem composes these steps at length >= 3,
where every legal one-label short replacement preserves A1--A3.

No global target in the SOURCE cycle, no conditional final
supremeness axiom, and no appendix theorem are used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Replacing just one occurrence by a genuine physical edge has
exactly the arbitrary replacement word with that one short piece
and all other occurrences kept. In particular, no connectors are
removed, invented or reordered. -/
theorem BigCycle.replaceOne_physical_resultWord
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (e : E)
    (hPrev : C.label (trainCyclicPred k) ≠ Sum.inr e)
    (hNext : Sum.inr e ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident (.inr e) (C.connector k))
    (hRight : D.Incident (.inr e) (C.connector (trainCyclicPred k))) :
    let H := C.replaceOne D k (Sum.inr e)
      hPrev hNext hLeft hRight
    let first : Fin n → TrainSupremePiece E P :=
      fun j => if j = k then .short e else .keep
    List.ofFn (fun j : Fin n => (H.label j, H.connector j)) =
      C.resultWord D first := by
  let H := C.replaceOne D k (Sum.inr e)
    hPrev hNext hLeft hRight
  let first : Fin n → TrainSupremePiece E P :=
    fun j => if j = k then .short e else .keep
  have hPiece (j : Fin n) :
      C.pieceWord D j (first j) = [(H.label j, H.connector j)] := by
    by_cases hj : j = k
    · subst j
      simp [first, H, BigCycle.pieceWord, BigCycle.replaceOne,
        BigCycle.relabelSameConnectors, BigCycle.replaceLabelAt]
    · simp [first, H, BigCycle.pieceWord, BigCycle.replaceOne,
        BigCycle.relabelSameConnectors, BigCycle.replaceLabelAt, hj]
  change List.ofFn (fun j : Fin n => (H.label j, H.connector j)) =
    (List.ofFn (fun j => C.pieceWord D j (first j))).flatten
  simp_rw [hPiece]
  exact (flatten_ofFn_singleton
    (fun j : Fin n => (H.label j, H.connector j))).symm

/-- One physical short absorption reflects an indexed supreme label
back to the ORIGINAL cycle, provided it was acceptable. The new
supreme label need not have been selected before the absorption. -/
theorem BigCycle.supreme_pullback_one_physical_short
    {n : ℕ} (C : D.BigCycle n) (k : Fin n) (e : E)
    (hPrev : C.label (trainCyclicPred k) ≠ Sum.inr e)
    (hNext : Sum.inr e ≠ C.label (cyclicSucc k))
    (hLeft : D.Incident (.inr e) (C.connector k))
    (hRight : D.Incident (.inr e) (C.connector (trainCyclicPred k)))
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hSupreme : (C.replaceOne D k (Sum.inr e)
      hPrev hNext hLeft hRight).HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  let H := C.replaceOne D k (Sum.inr e)
    hPrev hNext hLeft hRight
  let first : Fin n → TrainSupremePiece E P :=
    fun j => if j = k then .short e else .keep
  have hGeom : C.LocalLongA2Geometry D first := by
    intro j a b p hLong
    by_cases hj : j = k
    · subst j
      simp [first] at hLong
    · simp [first, hj] at hLong
  have hWord : List.ofFn (fun j : Fin n =>
      (H.label j, H.connector j)) = C.resultWord D first :=
    C.replaceOne_physical_resultWord D k e
      hPrev hNext hLeft hRight
  obtain ⟨j, hDesignated, later, hPlan, hProduces⟩ := hSupreme
  obtain ⟨kC, _, hCSupreme⟩ :=
    C.supreme_of_arbitrary_literal_replacement
      D H hAccept hLinear first hGeom hWord
      j ⟨hDesignated, later, hPlan, hProduces⟩
  exact C.hasSimultaneousSupreme_of_hasSupremeAt D kC hCSupreme

/-- A finite sequence of actual single-edge absorptions, keeping
all original physical connectors and their cyclic positions. -/
inductive BigCycle.PhysicalShortReachable (D : OrderOneData V E I P)
    {n : ℕ} : D.BigCycle n → D.BigCycle n → Prop
  | refl (C : D.BigCycle n) :
      BigCycle.PhysicalShortReachable D C C
  | step (C : D.BigCycle n) (k : Fin n) (e : E)
      (hPrev : C.label (trainCyclicPred k) ≠ Sum.inr e)
      (hNext : Sum.inr e ≠ C.label (cyclicSucc k))
      (hLeft : D.Incident (.inr e) (C.connector k))
      (hRight : D.Incident (.inr e) (C.connector (trainCyclicPred k)))
      {H : D.BigCycle n}
      (tail : BigCycle.PhysicalShortReachable D
        (C.replaceOne D k (Sum.inr e)
          hPrev hNext hLeft hRight) H) :
      BigCycle.PhysicalShortReachable D C H

/-- At source length at least three, any finite chain of legal physical
single-edge absorptions reflects eventual full simultaneous supremeness
to the original cycle. No designated occurrence is fixed in advance.
This is the compositional form needed by descent on the number of
geometric owner segments. -/
theorem BigCycle.PhysicalShortReachable.supreme_pullback_of_three_le
    {n : ℕ} {C H : D.BigCycle n}
    (hReach : BigCycle.PhysicalShortReachable D C H)
    (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (hAccept : C.Acceptable)
    (hSupreme : H.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  revert hAccept hSupreme
  induction hReach with
  | refl C =>
      intro _ hSupreme
      exact hSupreme
  | @step C k e hPrev hNext hLeft hRight H tail ih =>
      intro hAccept hSupreme
      have hNextAccept :
          (C.replaceOne D k (Sum.inr e)
            hPrev hNext hLeft hRight).Acceptable :=
        C.replaceOne_acceptable_of_three_le_length
          D k (Sum.inr e) hn hPrev hNext hLeft hRight hAccept
      have hNextSupreme : (C.replaceOne D k (Sum.inr e)
          hPrev hNext hLeft hRight).HasSimultaneousSupreme :=
        ih hNextAccept hSupreme
      exact C.supreme_pullback_one_physical_short
        D k e hPrev hNext hLeft hRight
        hAccept hLinear hNextSupreme

end StructuralRamsey.Girth.OrderOneData
