import Girth.TrainInsertedConnectorNodup
import Girth.TrainOutputOldPos
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

/-!
# Circulation: legality of the output forces freshness of inserted wagons

Every replacement block keeps its original right connector, and each
long block inserts one additional wagon connector before it. A legal
output BigCycle has distinct connector positions.

Consequently a long piece CANNOT insert a wagon that is already an
original connector: this would repeat a connector in the literal word.
Thus the freshness premise used while CONSTRUCTING a BigCycle is
automatic once the resulting BigCycle is already known to exist.

The proof is a converse to the existing optionalConnectorWord_nodup
lemma. It uses neither source acceptability nor wagon linearity, and
does not confuse the construction and post-construction hypotheses.
There is no appendix input.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- Duplicate-free optional insertion words cannot insert an old
connector. Both same-block and distinct-block coincidences are
excluded directly by the flatten Nodup conditions. -/
theorem optionalConnectorWord_fresh_of_nodup
    (base : Fin n → α) (insert : Fin n → Option α)
    (hNodup : (optionalConnectorWord base insert).Nodup) :
    ∀ (i j : Fin n) (a : α),
      insert i = some a → a ≠ base j := by
  classical
  have hFlat :
      (List.ofFn (fun t : Fin n =>
        optionalConnectorBlock base insert t)).flatten.Nodup := by
    simpa only [optionalConnectorWord] using hNodup
  obtain ⟨hWithin, hBetween⟩ := List.nodup_flatten.mp hFlat
  have hPair :
      ∀ ⦃i j : Fin n⦄, i < j →
        List.Disjoint (optionalConnectorBlock base insert i)
          (optionalConnectorBlock base insert j) :=
    (List.pairwise_ofFn.mp hBetween)
  intro i j a hi haEq
  by_cases hij : i = j
  · subst j
    have hBlock : (optionalConnectorBlock base insert i).Nodup :=
      hWithin _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have hNe : a ≠ base i := by
      simpa [optionalConnectorBlock, hi] using hBlock
    exact hNe haEq
  · have ha : a ∈ optionalConnectorBlock base insert i := by
      simp [optionalConnectorBlock, hi]
    have hj : base j ∈ optionalConnectorBlock base insert j := by
      cases hp : insert j with
      | none => simp [optionalConnectorBlock, hp]
      | some b => simp [optionalConnectorBlock, hp]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := hPair hlt
      exact ((List.disjoint_left.mp hd) ha)
        (by simpa [haEq] using hj)
    · have hd := hPair hgt
      exact ((List.disjoint_left.mp hd) hj)
        (by simpa [haEq] using ha)

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An ACTUAL literal output BigCycle automatically certifies that
each inserted long-piece wagon was absent from the source connector
list. No output acceptability or PlanValid is required. -/
theorem BigCycle.longWagons_fresh_of_literalBigCycle
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces) :
    ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p := by
  have hB : (List.ofFn B.connector).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j h
    apply Fin.ext
    have hEq : (Fin.cast (by simp) i : Fin m) =
        (Fin.cast (by simp) j : Fin m) :=
      B.connector_injective (by simpa only [List.get_ofFn] using h)
    simpa using congrArg Fin.val hEq
  have hConnectors :
      List.ofFn B.connector =
        optionalConnectorWord C.connector (C.insertedConnector D pieces) := by
    calc
      List.ofFn B.connector =
          (List.ofFn (fun j : Fin m =>
            (B.label j, B.connector j))).map Prod.snd := by
              simp [List.map_ofFn, Function.comp_def]
      _ = (C.resultWord D pieces).map Prod.snd :=
            congrArg (List.map Prod.snd) hWord
      _ = optionalConnectorWord C.connector (C.insertedConnector D pieces) :=
            C.resultWord_connectorList D pieces
  have hNodup :
      (optionalConnectorWord C.connector
        (C.insertedConnector D pieces)).Nodup := by
    rw [← hConnectors]
    exact hB
  intro i e p f hp t
  have hSome :
      C.insertedConnector D pieces i = some (Sum.inr p) := by
    simp [BigCycle.insertedConnector, hp]
  exact (optionalConnectorWord_fresh_of_nodup
    C.connector (C.insertedConnector D pieces)
    hNodup i t (Sum.inr p) hSome).symm

/-- The built-in global-word obligation in HasSupremeAt itself
supplies freshness. This removes a redundant premise in any later
proof that starts from an already-established supreme output. -/
theorem BigCycle.freshness_of_hasSupremeAt
    {n : ℕ} (C : D.BigCycle n) (k : Fin n)
    (h : C.HasSupremeAt D k) :
    ∃ pieces : Fin n → TrainSupremePiece E P,
      C.PlanValid D k pieces ∧ C.PlanProducesBigCycle D pieces ∧
      (∀ (i : Fin n) (e : E) (p : P) (f : E),
        pieces i = .long e p f →
        ∀ t : Fin n, C.connector t ≠ Sum.inr p) := by
  obtain ⟨_hk, pieces, hPlan, m, B, hWord⟩ := h
  exact ⟨pieces, hPlan, ⟨m, B, hWord⟩,
    C.longWagons_fresh_of_literalBigCycle D B pieces hWord⟩

end OrderOneData
end StructuralRamsey.Girth
