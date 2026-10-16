import Girth.TrainSimultaneousSupreme
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Flatten
import Mathlib.Tactic

/-!
# Circulation: old connector positions inside a literal replacement word

Every replacement piece retains its source right-hand connector. A
long piece may insert a fresh wagon before that connector, but no
piece inserts a new VERTEX connector.

For an actual output BigCycle whose complete label/connector word
is the literal resultWord of the source, these two elementary facts
yield a map oldPos : Fin n → Fin m of old connector positions into
the output: each old connector occurs at its chosen output position,
and every output VERTEX position lies in this image.

Connector injectivity of the actual output BigCycle makes the chosen
oldPos unique on old connectors; no explicit prefix-length arithmetic
or new indexing convention is required.

Wagon-vertex contacts then automatically pull back through oldPos,
because their physical OrderOneData is unchanged. These conclusions
provide the exact hConnector/hContactPullback/hVertexPos interface
needed for the separate A2 (#538) and A3 (#537) transfer proofs.

No output acceptability, wagon linearity, freshness, supreme-plan
assumption, or appendix theorem is used: only the literal output
BigCycle word, which is already obtained by checked #534.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every original connector occurs in the actual expanded word,
at the end of its own short, retained or long replacement block. -/
theorem BigCycle.source_connector_mem_resultWord
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) (i : Fin n) :
    ∃ a : I ⊕ E,
      (a, C.connector i) ∈ C.resultWord D pieces := by
  classical
  unfold BigCycle.resultWord
  cases hp : pieces i with
  | keep =>
      refine ⟨C.label i, List.mem_flatten.mpr ?_⟩
      refine ⟨C.pieceWord D i (pieces i), ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · simp [BigCycle.pieceWord, hp]
  | short e =>
      refine ⟨Sum.inr e, List.mem_flatten.mpr ?_⟩
      refine ⟨C.pieceWord D i (pieces i), ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · simp [BigCycle.pieceWord, hp]
  | long e w f =>
      refine ⟨Sum.inr f, List.mem_flatten.mpr ?_⟩
      refine ⟨C.pieceWord D i (pieces i), ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · simp [BigCycle.pieceWord, hp]

/-- A vertex connector in the resultWord must already be a SOURCE
vertex connector: the only newly inserted connectors are wagons.
This is a statement about the actual flattened word, not just
the separate list of new wagons. -/
theorem BigCycle.resultWord_vertex_from_source
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (a : I ⊕ E) (x : V)
    (hMem : (a, Sum.inl x) ∈ C.resultWord D pieces) :
    ∃ i : Fin n, C.connector i = Sum.inl x := by
  classical
  unfold BigCycle.resultWord at hMem
  obtain ⟨block, hBlock, hEntry⟩ := List.mem_flatten.mp hMem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hBlock
  cases hp : pieces i with
  | keep =>
      have hEq : (a, Sum.inl x) = (C.label i, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      exact ⟨i, (congrArg Prod.snd hEq).symm⟩
  | short e =>
      have hEq : (a, Sum.inl x) = (Sum.inr e, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      exact ⟨i, (congrArg Prod.snd hEq).symm⟩
  | long e w f =>
      have hCases :
          (a, Sum.inl x) = (Sum.inr e, Sum.inr w) ∨
          (a, Sum.inl x) = (Sum.inr f, C.connector i) := by
        simpa [BigCycle.pieceWord, hp] using hEntry
      rcases hCases with hNew | hOld
      · have hBad : (Sum.inl x : V ⊕ P) = Sum.inr w :=
          congrArg Prod.snd hNew
        cases hBad
      · exact ⟨i, (congrArg Prod.snd hOld).symm⟩

/-- An arbitrary actual BigCycle with the literal expansion word
already contains an oldPos map respecting EVERY source connector,
and every output vertex connector lies in the image of this map.
No prefix-sum construction, extra injection premise, or output
acceptability is needed. -/
theorem BigCycle.oldPos_exists_of_literal_resultWord
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    ∃ oldPos : Fin n → Fin m,
      (∀ i : Fin n, B.connector (oldPos i) = C.connector i) ∧
      (∀ (j : Fin m) (x : V),
        B.connector j = Sum.inl x →
        ∃ i : Fin n, j = oldPos i) := by
  classical
  have hSome : ∀ i : Fin n,
      ∃ j : Fin m, B.connector j = C.connector i := by
    intro i
    obtain ⟨a, ha⟩ := C.source_connector_mem_resultWord D pieces i
    rw [← hWord] at ha
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp ha
    exact ⟨j, congrArg Prod.snd hj⟩
  let oldPos : Fin n → Fin m := fun i => Classical.choose (hSome i)
  have hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i :=
    fun i => Classical.choose_spec (hSome i)
  refine ⟨oldPos, hConnector, ?_⟩
  intro j x hBx
  have hBMem : (B.label j, Sum.inl x) ∈ C.resultWord D pieces := by
    rw [← hWord]
    simpa [hBx] using
      (List.mem_ofFn.mpr ⟨j, rfl⟩ :
        (B.label j, B.connector j) ∈
          List.ofFn (fun t : Fin m => (B.label t, B.connector t)))
  obtain ⟨i, hCi⟩ :=
    C.resultWord_vertex_from_source D pieces (B.label j) x hBMem
  refine ⟨i, ?_⟩
  apply B.connector_injective
  calc
    B.connector j = Sum.inl x := hBx
    _ = C.connector i := hCi.symm
    _ = B.connector (oldPos i) := (hConnector i).symm

/-- With the same physical pretrain on both sides, the oldPos map
above automatically pulls back every output wagon-vertex contact.
This is precisely the shared bookkeeping interface needed for
the separate A2 and A3 transfer arguments. -/
theorem BigCycle.oldPos_contacts_of_literal_resultWord
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    ∃ oldPos : Fin n → Fin m,
      (∀ i : Fin n, B.connector (oldPos i) = C.connector i) ∧
      (∀ (j : Fin m) (x : V),
        B.connector j = Sum.inl x →
        ∃ i : Fin n, j = oldPos i) ∧
      (∀ (p : P) (j : Fin m), B.InWagonAt p j →
        ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i) := by
  obtain ⟨oldPos, hConnector, hVertex⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  refine ⟨oldPos, hConnector, hVertex, ?_⟩
  intro p j hContact
  obtain ⟨x, hBx, hPx⟩ := hContact
  obtain ⟨i, hPos⟩ := hVertex j x hBx
  refine ⟨i, hPos, x, ?_, hPx⟩
  calc
    C.connector i = B.connector (oldPos i) := (hConnector i).symm
    _ = B.connector j := congrArg B.connector hPos.symm
    _ = Sum.inl x := hBx

end StructuralRamsey.Girth.OrderOneData
