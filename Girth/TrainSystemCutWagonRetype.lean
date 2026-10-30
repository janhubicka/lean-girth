import Girth.TrainSystemCutWagonSeed
import Girth.TrainArbitraryDesignatedOrigin
import Mathlib.Tactic

/-!
# Remove the temporary wagon-copy sort after physical expansion

The auxiliary wagonSeed from TrainSystemCutWagonSeed is used only to
apply the checked arbitrary-replacement theorem. Once all temporary
designated occurrences are replaced by physical short/long pieces,
the result contains ONLY actual edge labels.

This file proves:
* no new designated label can appear in a literal expanded word when
  every original temporary wagon occurrence was replaced;
* the resulting edge-only BigCycle can be retyped from the temporary
  wagon-copy sort back to the original system, keeping every connector
  and every numerical weight exactly;
* A2 and A3 are unaffected because the physical edge carriers and
  wagon parent map were not modified. A1 is preserved away from order 1.

No copied wagon is mistaken for an original designated B occurrence.
The geometric choice of short or long pieces is a separate theorem.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- When no auxiliary wagon-source occurrence is retained, every
literal output occurrence has an ACTUAL edge label. -/
theorem BigCycle.output_edgeOnly_of_no_keeps
    {n m : ℕ} (C : (D.wagonSeed).BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hNone : ∀ i : Fin n, pieces i ≠ .keep)
    (B : (D.wagonSeed).BigCycle m)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord (D.wagonSeed) pieces) :
    ∀ j : Fin m, ∃ e : E, B.label j = Sum.inr e := by
  intro j
  cases hl : B.label j with
  | inr e =>
      exact ⟨e, rfl⟩
  | inl p =>
      have hd : (D.wagonSeed).designated (B.label j) := by
        simp [hl, OrderOneData.designated]
      obtain ⟨oldPos, hConn, _⟩ :=
        C.oldPos_exists_of_literal_resultWord (D.wagonSeed) B pieces hWord
      obtain ⟨i, _, hKeep, _⟩ :=
        C.output_designated_origin_of_literalWord
          (D.wagonSeed) B pieces hWord oldPos hConn j hd
      exact (hNone i hKeep).elim

/-- An edge-only cycle in the temporary wagon-copy pretrain is a
literal cycle in the ORIGINAL pretrain. Its occurrence labels are
retagged from P⊕E to I⊕E; all vertices, wagons and original edges
are unchanged. -/
noncomputable def BigCycle.retypeWagonSeedEdgeOnly
    {n : ℕ} (B : (D.wagonSeed).BigCycle n)
    (hOnly : ∀ j : Fin n, ∃ e : E, B.label j = Sum.inr e) :
    D.BigCycle n := by
  classical
  let edge : Fin n → E := fun j => Classical.choose (hOnly j)
  have he : ∀ j : Fin n, B.label j = Sum.inr (edge j) :=
    fun j => Classical.choose_spec (hOnly j)
  exact {
    length_ge_two := B.length_ge_two
    label := fun j => Sum.inr (edge j)
    connector := B.connector
    adjacent_ne := by
      intro i hh
      apply B.adjacent_ne i
      calc
        B.label i = Sum.inr (edge i) := he i
        _ = Sum.inr (edge (cyclicSucc i)) :=
           congrArg (Sum.inr : E → P ⊕ E) (Sum.inr.inj hh)
        _ = B.label (cyclicSucc i) := (he _).symm
    connector_injective := B.connector_injective
    left_incident := by
      intro i
      have h := B.left_incident i
      rw [he i] at h
      exact h
    right_incident := by
      intro i
      have h := B.right_incident i
      rw [he (cyclicSucc i)] at h
      exact h }

/-- The retagged BigCycle has precisely the original physical connectors
and numerical twice-order. -/
theorem BigCycle.retypeWagonSeedEdgeOnly_twiceOrder
    {n : ℕ} (B : (D.wagonSeed).BigCycle n)
    (hOnly : ∀ j : Fin n, ∃ e : E, B.label j = Sum.inr e) :
    (B.retypeWagonSeedEdgeOnly D hOnly).twiceOrder = B.twiceOrder := rfl

/-- A2/A3 transfer definitionally; the order-not-one hypothesis
supplies A1 because the output contains no designated labels.
Numerical order is unchanged exactly. -/
theorem BigCycle.retypeWagonSeedEdgeOnly_acceptable
    {n : ℕ} (B : (D.wagonSeed).BigCycle n)
    (hOnly : ∀ j : Fin n, ∃ e : E, B.label j = Sum.inr e)
    (hAcc : B.Acceptable) (hOrder : B.twiceOrder ≠ 2) :
    (B.retypeWagonSeedEdgeOnly D hOnly).Acceptable := by
  let C : D.BigCycle n := B.retypeWagonSeedEdgeOnly D hOnly
  have hA1 : C.A1 := by
    intro hOne
    exfalso
    apply hOrder
    exact (B.retypeWagonSeedEdgeOnly_twiceOrder D hOnly).symm.trans hOne
  have hA2 : C.A2 := hAcc.2.1
  have hA3 : C.A3 := hAcc.2.2
  exact ⟨hA1, hA2, hA3⟩

/-- Every retyped occurrence is a physical edge of the ORIGINAL
system, not a designated label introduced in the auxiliary system. -/
theorem BigCycle.retypeWagonSeedEdgeOnly_only_edges
    {n : ℕ} (B : (D.wagonSeed).BigCycle n)
    (hOnly : ∀ j : Fin n, ∃ e : E, B.label j = Sum.inr e) :
    ∀ j : Fin n,
      ∃ e : E, (B.retypeWagonSeedEdgeOnly D hOnly).label j = Sum.inr e := by
  intro j
  exact ⟨Classical.choose (hOnly j), rfl⟩

end StructuralRamsey.Girth.OrderOneData
