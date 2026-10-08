import Girth.ForestNeutralHistory
import Girth.ForestDiaryCommonChoice
import Mathlib.Tactic

/-!
# Simultaneous neutral-gap replay of finitely many marked histories

A marked history remembers exactly the code inserted at a designated
level m. All subsequent codes avoid that level as an ancestor parameter.
The code recorded at m is allowed to depend on the level-m history
prefix, but histories with equal prefixes must prescribe equal codes.

Under this finite compatibility condition, a single global one-gap
shape map has shorter preimages of all the marked histories.

This is a syntactic normal-form lemma. It does not prove the bounded
active-event guard for actual B-copies or a faithful geometric
interpretation of carrier births.
-/

namespace StructuralRamsey.Girth

open SuccessorTree.FreeAncestral

universe u
variable {Label : Type u} {arity : ℕ} [Fintype Label] [Nonempty Label]

/-- One target history with a designated inserted code at level m.
The compatibility field says that replay by any choice function
taking the recorded value at the stem is legal. -/
structure MarkedNeutralGap (m k : ℕ) where
  history : History Label arity (m + k + 1)
  stem : History Label arity m
  insertedCode : Code Label arity m
  compatible :
    ∀ choose : History Label arity m → Code Label arity m,
      choose stem = insertedCode →
        NeutralGapTail m choose k history

namespace MarkedNeutralGap

/-- A one-step history is automatically compatible with insertion
of its own first code. -/
def singleton (m : ℕ)
    (stem : History Label arity m)
    (code : Code Label arity m) :
    MarkedNeutralGap (Label := Label) (arity := arity) m 0 where
  history := History.step stem code
  stem := stem
  insertedCode := code
  compatible := by
    intro choose hc
    change NeutralGapTail m choose 0 (History.step stem code)
    rw [← hc]
    exact NeutralGapTail.base stem

/-- Adding one later transition with no parameter at the skipped
target level preserves neutral-gap compatibility. -/
def extend
    {m k : ℕ}
    (M : MarkedNeutralGap (Label := Label) (arity := arity) m k)
    (code : Code Label arity (m + k + 1))
    (hAvoid :
      ∀ j : Fin code.params.len.val,
        (code.params.value j).val ≠ m) :
    MarkedNeutralGap (Label := Label) (arity := arity) m (k + 1) where
  history := History.step M.history code
  stem := M.stem
  insertedCode := M.insertedCode
  compatible := by
    intro choose hc
    exact NeutralGapTail.step
      (M.compatible choose hc) code hAvoid

end MarkedNeutralGap

/-- Every finite family of marked histories with mutually consistent
insertion codes has shorter preimages under *one and the same* global
one-gap map. This is the common-branch compatibility step of the
guarded finite-presentation argument. -/
theorem finiteMarkedNeutralGap_preimages
    (m k q : ℕ)
    (P : Fin q →
      MarkedNeutralGap (Label := Label) (arity := arity) m k)
    (hConsistent :
      ∀ i j : Fin q, (P i).stem = (P j).stem →
        (P i).insertedCode = (P j).insertedCode) :
    ∃ choose :
        History Label arity m → Code Label arity m,
      ∃ s : Fin q → History Label arity (m + k),
        ∀ i : Fin q,
          gapNode m choose
            (⟨m + k, s i⟩ : Node Label arity) =
            (⟨m + k + 1, (P i).history⟩ :
              Node Label arity) := by
  classical
  letI : Nonempty (Code Label arity m) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Label),
      emptyParamTuple arity m⟩⟩
  obtain ⟨choose, hc⟩ :=
    exists_commonNeutralGapChoice
      (Label := Label) arity m q
      (fun i => (P i).stem)
      (fun i => (P i).insertedCode)
      hConsistent
  have hLegal (i : Fin q) :
      NeutralGapTail m choose k (P i).history :=
    (P i).compatible choose (hc i)
  obtain ⟨s, hs⟩ :=
    neutralGapTail_finite_preimages
      m choose k q (fun i => (P i).history) hLegal
  exact ⟨choose, s, hs⟩

end StructuralRamsey.Girth
