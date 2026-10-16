import Girth.TrainOutputA1Length

/-!
# Circulation: provenance of designated labels in expanded supreme plans

A selected simultaneous supreme plan keeps precisely the occurrences
of its chosen designated source label. Every other source occurrence
is replaced by one or two ACTUAL EDGE labels.

Therefore the expanded output word contains no other designated label:
any designated occurrence in a resulting BigCycle is the same chosen
source label, with exactly the original index value.

This avoids an unnecessary second-collapse composition argument in the
special case of a simultaneous supreme plan. The broader manuscript
admissible-replacement lemma may retain other designated labels, so
this theorem must NOT be applied to arbitrary replacement plans.

No global output acceptability, output wagon linearity, or appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every designated entry of one local PlanValid replacement block
must be a kept copy of the chosen supreme source label. -/
theorem BigCycle.designated_pieceWord_label_eq_target
    {n : ℕ} (C : D.BigCycle n) (k j : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (a : I ⊕ E) (q : V ⊕ P)
    (ha : D.designated a)
    (hMem : (a,q) ∈ C.pieceWord D j (pieces j)) :
    a = C.label k := by
  cases hp : pieces j with
  | keep =>
      have heq : (a,q) = (C.label j, C.connector j) := by
        simpa [BigCycle.pieceWord, hp] using hMem
      calc
        a = C.label j := congrArg Prod.fst heq
        _ = C.label k := C.label_eq_supreme_of_keep D k j pieces hPlan hp
  | short e =>
      cases a with
      | inl i =>
          have hcontra : False := by
            simpa [BigCycle.pieceWord, hp] using hMem
          exact False.elim hcontra
      | inr e =>
          simp [designated] at ha
  | long e w f =>
      cases a with
      | inl i =>
          have hcontra : False := by
            simpa [BigCycle.pieceWord, hp] using hMem
          exact False.elim hcontra
      | inr e =>
          simp [designated] at ha

/-- The literal expanded word carries just ONE designated source label,
the chosen supreme copy, regardless of how many short/long pieces
were inserted or whether the word has been shown globally legal. -/
theorem BigCycle.designated_resultWord_label_eq_target
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (a : I ⊕ E) (q : V ⊕ P)
    (ha : D.designated a)
    (hMem : (a,q) ∈ C.resultWord D pieces) :
    a = C.label k := by
  obtain ⟨block, hBlock, hInside⟩ := List.mem_flatten.mp hMem
  obtain ⟨j, hEq⟩ := List.mem_ofFn.mp hBlock
  have hIn : (a,q) ∈ C.pieceWord D j (pieces j) := by
    simpa [BigCycle.resultWord, hEq] using hInside
  exact C.designated_pieceWord_label_eq_target D k j pieces hPlan
    a q ha hIn

/-- A designated label anywhere in the actual expanded BigCycle is
necessarily the original chosen source label. Other designated
source labels CANNOT survive a strict PlanValid supreme collapse. -/
theorem BigCycle.output_designated_label_eq_target
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (k : Fin n) (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hWord : List.ofFn (fun i : Fin m =>
      (B.label i, B.connector i)) = C.resultWord D pieces)
    (i : Fin m) (hDes : D.designated (B.label i)) :
    B.label i = C.label k := by
  have hMem : (B.label i, B.connector i) ∈ C.resultWord D pieces := by
    rw [← hWord]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact C.designated_resultWord_label_eq_target D k pieces hPlan
    (B.label i) (B.connector i) hDes hMem

end StructuralRamsey.Girth.OrderOneData
