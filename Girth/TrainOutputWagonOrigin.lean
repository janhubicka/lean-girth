import Girth.TrainOutputOldPos
import Girth.TrainLongBoundaryCollision

/-!
# Circulation: classify wagon connectors in the literal replacement word

Every occurrence of a wagon connector in the actual output BigCycle
comes from one of exactly two PHYSICAL sources:
* the unchanged old right connector of a retained/short/long block; or
* the fresh wagon inserted as the first connector of a genuine long block.

With an oldPos map from the checked literal-word interface, the first
case determines the EXACT output position of the inherited wagon by
connector injectivity. The second case identifies an actual source
LongValid piece and its freshness under PlanValid.

This is a classification of wagon ORIGIN, not yet the successor and
predecessor position equations required by the conditional A2 theorem.
No output A2/A3/Acceptable, output wagon linearity, or appendix theorem
is used here.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every actual output wagon connector is either an inherited old
connector at its correctly matched oldPos position, or the fresh
connector of a specifically identified long replacement block.

Only literal word equality and the two source/output connector maps
are used. There is no PlanValid or geometric bound hypothesis. -/
theorem BigCycle.output_wagon_old_or_long_of_literal_word
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (j : Fin m) (p : P)
    (hj : B.connector j = Sum.inr p) :
    (∃ i : Fin n, j = oldPos i ∧ C.connector i = Sum.inr p) ∨
    (∃ (i : Fin n) (e f : E), pieces i = .long e p f) := by
  classical
  have hMember : (B.label j, Sum.inr p) ∈ C.resultWord D pieces := by
    rw [← hWord]
    simpa [hj] using
      (List.mem_ofFn.mpr ⟨j, rfl⟩ :
        (B.label j, B.connector j) ∈
          List.ofFn (fun t : Fin m => (B.label t, B.connector t)))
  unfold BigCycle.resultWord at hMember
  obtain ⟨block, hBlock, hEntry⟩ := List.mem_flatten.mp hMember
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hBlock
  have hOldCase (hi : C.connector i = Sum.inr p) :
      (∃ t : Fin n, j = oldPos t ∧ C.connector t = Sum.inr p) := by
    refine ⟨i, ?_, hi⟩
    apply B.connector_injective
    calc
      B.connector j = Sum.inr p := hj
      _ = C.connector i := hi.symm
      _ = B.connector (oldPos i) := (hConnector i).symm
  cases hp : pieces i with
  | keep =>
      have heq :
          (B.label j, Sum.inr p) =
            (C.label i, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      exact Or.inl (hOldCase (congrArg Prod.snd heq).symm)
  | short e =>
      have heq :
          (B.label j, Sum.inr p) =
            (Sum.inr e, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      exact Or.inl (hOldCase (congrArg Prod.snd heq).symm)
  | long e w f =>
      have hCases :
          (B.label j, Sum.inr p) = (Sum.inr e, Sum.inr w) ∨
          (B.label j, Sum.inr p) = (Sum.inr f, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      rcases hCases with hNew | hOld
      · have hpw : p = w := Sum.inr.inj (congrArg Prod.snd hNew)
        subst w
        exact Or.inr ⟨i, e, f, hp⟩
      · exact Or.inl (hOldCase (congrArg Prod.snd hOld).symm)

/-- A valid strict supreme plan upgrades the literal two-case source
classification to a genuine LongValid source piece with exactly the
specified fresh physical wagon. No additional unproved local geometry
is introduced in this upgrade. -/
theorem BigCycle.output_wagon_old_or_valid_long
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (j : Fin m) (p : P)
    (hj : B.connector j = Sum.inr p) :
    (∃ i : Fin n, j = oldPos i ∧ C.connector i = Sum.inr p) ∨
    (∃ (i : Fin n) (e f : E),
      C.LongValid D k i e p f ∧
      ∀ t : Fin n, C.connector t ≠ Sum.inr p) := by
  rcases C.output_wagon_old_or_long_of_literal_word
      D B pieces hWord oldPos hConnector j p hj with
    hOld | ⟨i, e, f, hi⟩
  · exact Or.inl hOld
  · exact Or.inr ⟨i, e, f,
      C.longValid_of_piece_eq_long D k i pieces hPlan e f p hi,
      hFresh i e p f hi⟩

/-- A wagon that was already a SOURCE connector cannot originate from
any inserted long piece; freshness makes the source/output classification
exclusive at that wagon. -/
theorem BigCycle.output_old_wagon_inherited
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (j : Fin m) (p : P)
    (hj : B.connector j = Sum.inr p)
    (hOld : ∃ i : Fin n, C.connector i = Sum.inr p) :
    ∃ i : Fin n, j = oldPos i ∧ C.connector i = Sum.inr p := by
  rcases C.output_wagon_old_or_long_of_literal_word
      D B pieces hWord oldPos hConnector j p hj with
    hInherit | ⟨i, e, f, hPiece⟩
  · exact hInherit
  · obtain ⟨t, ht⟩ := hOld
    exact False.elim ((hFresh i e p f hPiece t) ht)


/-- Every selected long piece contributes its fresh wagon connector to
the ACTUAL output word. The proof does not assume a preselected
output index, wagon-covering condition or output acceptability. -/
theorem BigCycle.selected_long_wagon_occurs_in_output
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (i : Fin n) (e f : E) (p : P)
    (hPiece : pieces i = .long e p f) :
    ∃ j : Fin m, B.connector j = Sum.inr p := by
  classical
  have hMem : (Sum.inr e, Sum.inr p) ∈ C.resultWord D pieces := by
    unfold BigCycle.resultWord
    apply List.mem_flatten.mpr
    refine ⟨C.pieceWord D i (pieces i), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · simp [BigCycle.pieceWord, hPiece]
  rw [← hWord] at hMem
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hMem
  exact ⟨j, congrArg Prod.snd hj⟩

/-- A real source LongValid piece provides all the geometric witness
data demanded by the A3 split-transfer interface, including an
ACTUAL output wagon connector, without assuming output A3. -/
theorem BigCycle.selected_long_A3_split_witness
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (k i : Fin n) (e f : E) (p : P)
    (hPiece : pieces i = .long e p f)
    (hLong : C.LongValid D k i e p f) :
    ∃ (q : P) (x y : V),
      C.connector (trainCyclicPred i) = Sum.inl x ∧
      C.connector i = Sum.inl y ∧
      D.WagonVertex q x ∧ D.WagonVertex q y ∧
      ∃ j : Fin m, B.connector j = Sum.inr q := by
  obtain ⟨x, y, hx, hy, _he, _hf, _hne, hep, hfp,
    hxe, hyf, _hNoPair⟩ := hLong
  refine ⟨p, x, y, hx, hy, ⟨e, hep, hxe⟩,
    ⟨f, hfp, hyf⟩, ?_⟩
  exact C.selected_long_wagon_occurs_in_output
    D B pieces hWord i e f p hPiece

end StructuralRamsey.Girth.OrderOneData
