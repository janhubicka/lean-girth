import Girth.TrainSimultaneousSupreme
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a FIXED two-vertex two-occurrence supreme plan is a short or long

At two occurrences, choose the ACTUAL designated target and preserve
its SPECIFIED PlanValid pieces. The other reduced occurrence has
boundary connectors x and y, both vertices. Its chosen piece must be:
  * SHORT, yielding a genuine ambient A-edge joining x and y; or
  * LONG, carrying the actual no-pair-edge condition for x,y.
These cases are mutually exclusive. In particular the existence of a
physical x--y edge forces the EXISTING chosen piece to be short, and
the absence of such an edge forces it to be long. No plan is reselected.

This does not construct a new physical original-source replacement,
choose a different supreme standard, identify original B labels with
geometric owners, or resolve the long two-cut orientation obstruction.
Circulation only; no appendix or manuscript edits.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- At two reduced occurrences with vertex boundaries, a specified
valid supreme plan has at its other position EXACTLY one of the two
geometric piece types, separated by the true ambient pair-edge test. -/
theorem BigCycle.fixed_two_vertex_plan_short_or_long
    (Z : D.BigCycle 2) (target : Fin 2)
    (x y : V)
    (hx : Z.connector target = Sum.inl x)
    (hy : Z.connector (cyclicSucc target) = Sum.inl y)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : Z.PlanValid D target pieces) :
    ((∃ e : E, pieces (cyclicSucc target) = .short e) ∧
      D.PairEdge x y) ∨
    ((∃ (e : E) (w : P) (f : E),
       pieces (cyclicSucc target) = .long e w f) ∧
      ¬ D.PairEdge x y) := by
  let j : Fin 2 := cyclicSucc target
  have hPred : trainCyclicPred j = target := by
    dsimp [j]
    exact trainCyclicPred_cyclicSucc_of_two_le
      (by decide : 2 ≤ 2) target
  have hDiff : Z.label j ≠ Z.label target := by
    dsimp [j]
    exact (Z.adjacent_ne target).symm
  have hValid := (hPlan j).2 hDiff
  cases hp : pieces j with
  | keep =>
      simp only [hp] at hValid
  | short e =>
      have hShort : Z.ShortValid D target j e := by
        simpa only [hp] using hValid
      have hxE : x ∈ D.edgeCarrier e := by
        have hLeft := hShort.2.1
        rw [hPred, hx] at hLeft
        simpa only [Incident, carrier] using hLeft
      have hyE : y ∈ D.edgeCarrier e := by
        have hRight := hShort.2.2
        change Z.connector j = Sum.inl y at hy
        rw [hy] at hRight
        simpa only [Incident, carrier] using hRight
      exact Or.inl ⟨⟨e, by simpa [j] using hp⟩,
        ⟨e, hxE, hyE⟩⟩
  | long e w f =>
      have hLong : Z.LongValid D target j e w f := by
        simpa only [hp] using hValid
      obtain ⟨x', y', hLeft, hRight, _he, _hf,
        _hne, _hParentE, _hParentF, _hxE, _hyF, hNoPair⟩ := hLong
      have hxx : x' = x := by
        have hSum : (Sum.inl x' : V ⊕ P) = Sum.inl x := by
          calc
            Sum.inl x' = Z.connector (trainCyclicPred j) := hLeft.symm
            _ = Z.connector target := by rw [hPred]
            _ = Sum.inl x := hx
        exact Sum.inl.inj hSum
      have hyy : y' = y := by
        have hSum : (Sum.inl y' : V ⊕ P) = Sum.inl y := by
          calc
            Sum.inl y' = Z.connector j := hRight.symm
            _ = Sum.inl y := by simpa [j] using hy
        exact Sum.inl.inj hSum
      have hNo : ¬ D.PairEdge x y := by
        simpa only [hxx, hyy] using hNoPair
      exact Or.inr ⟨⟨e, w, f, by simpa [j] using hp⟩, hNo⟩

/-- In a SPECIFIED globally legal reduced plan, an ambient x--y edge
forces the other occurrence to be replaced by a physical short. -/
theorem BigCycle.fixed_two_vertex_plan_short_of_pairEdge
    (Z : D.BigCycle 2) (target : Fin 2)
    (x y : V)
    (hx : Z.connector target = Sum.inl x)
    (hy : Z.connector (cyclicSucc target) = Sum.inl y)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : Z.PlanValid D target pieces)
    (hPair : D.PairEdge x y) :
    ∃ e : E, pieces (cyclicSucc target) = .short e := by
  rcases BigCycle.fixed_two_vertex_plan_short_or_long D Z
    target x y hx hy pieces hPlan with hShort | hLong
  · exact hShort.1
  · exact False.elim (hLong.2 hPair)

/-- Conversely, in the ABSENCE of an ambient x--y edge, the
specified reduced plan must use a genuine long piece at the other
occurrence. -/
theorem BigCycle.fixed_two_vertex_plan_long_of_no_pairEdge
    (Z : D.BigCycle 2) (target : Fin 2)
    (x y : V)
    (hx : Z.connector target = Sum.inl x)
    (hy : Z.connector (cyclicSucc target) = Sum.inl y)
    (pieces : Fin 2 → TrainSupremePiece E P)
    (hPlan : Z.PlanValid D target pieces)
    (hNoPair : ¬ D.PairEdge x y) :
    ∃ (e : E) (w : P) (f : E),
      pieces (cyclicSucc target) = .long e w f := by
  rcases BigCycle.fixed_two_vertex_plan_short_or_long D Z
    target x y hx hy pieces hPlan with hShort | hLong
  · exact False.elim (hNoPair hShort.2)
  · exact hLong.1

end StructuralRamsey.Girth.OrderOneData
