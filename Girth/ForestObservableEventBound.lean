import Girth.ForestObservableProfile
import Mathlib.Tactic

/-!
# Bounded observable changes along a train history

Fix q marked copies of one finite B with v vertices and e support
edges. At any intermediate picture, record:

* equality relations among the q*v labelled B-vertices, represented
  as an ordered-pair relation; and
* which of the q*e marked support-edge occurrences has been born.

There are (q*v)^2 + q*e possible atomic entries.

If the records grow monotonically, the number of stages introducing
at least one genuinely new observable entry is bounded by this number,
independently of the length of the construction. This does NOT show
that every nonneutral intrinsic successor event changes such an entry;
that is the geometric diary-coding obligation still open.
-/

namespace StructuralRamsey.Girth

/-- Potentially observable equalities and support births in q marked
copies of a finite B with v vertices and e support edges. -/
abbrev ForestObservableAtom (q v e : ℕ) : Type :=
  ((Fin q × Fin v) × (Fin q × Fin v)) ⊕ (Fin q × Fin e)

theorem forestObservableAtom_card (q v e : ℕ) :
    Fintype.card (ForestObservableAtom q v e) =
      (q * v) * (q * v) + q * e := by
  simp [ForestObservableAtom]

/-- A strictly increasing finite chain of finite subsets of one finite
alphabet has at most as many steps as there are possible records. -/
theorem strictRecordChain_length_le
    {α : Type*} [Fintype α]
    (R : ℕ → Finset α)
    (N : ℕ)
    (hStrict : ∀ i : ℕ, i < N → R i ⊂ R (i + 1)) :
    N ≤ Fintype.card α := by
  classical
  have hPrefix :
      ∀ n : ℕ, n ≤ N → n ≤ (R n).card := by
    intro n
    induction n with
    | zero =>
        intro _
        omega
    | succ n ih =>
        intro hn
        have hPrev := ih (by omega)
        have hIncrease :
            (R n).card < (R (n + 1)).card :=
          Finset.card_lt_card (hStrict n (by omega))
        omega
  have hMax : (R N).card ≤ Fintype.card α :=
    Finset.card_le_univ (R N)
  have hN := hPrefix N le_rfl
  omega

/-- Marked observable events include only the steps whose record changes
strictly; arbitrarily many neutral stages may occur between them. -/
theorem activeRecordSteps_le
    {α : Type*} [Fintype α]
    (R : ℕ → Finset α)
    (active : ℕ → Prop) [DecidablePred active]
    (N : ℕ)
    (hMono : ∀ i : ℕ, i < N → R i ⊆ R (i + 1))
    (hActive :
      ∀ i : ℕ, i < N → active i → R i ⊂ R (i + 1)) :
    ((Finset.range N).filter active).card ≤ Fintype.card α := by
  classical
  have hPrefix :
      ∀ n : ℕ, n ≤ N →
        ((Finset.range n).filter active).card ≤ (R n).card := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hPrev := ih (by omega)
        have hMonoCard :
            (R n).card ≤ (R (n + 1)).card :=
          Finset.card_le_card (hMono n (by omega))
        have hStep :
            ((Finset.range (n + 1)).filter active).card =
              ((Finset.range n).filter active).card +
                (if active n then 1 else 0) := by
          by_cases ha : active n
          · simp [Finset.range_add_one, Finset.filter_insert, ha]
          · simp [Finset.range_add_one, Finset.filter_insert, ha]
        rw [hStep]
        by_cases ha : active n
        · have hIncrease :
              (R n).card < (R (n + 1)).card :=
            Finset.card_lt_card (hActive n (by omega) ha)
          simp only [if_pos ha]
          omega
        · simp only [if_neg ha]
          omega
  have hN := hPrefix N le_rfl
  have hMax : (R N).card ≤ Fintype.card α :=
    Finset.card_le_univ (R N)
  omega

/-- In a q-copy train, active steps which *strictly add a labelled
equality or marked-edge birth* are bounded by the size of the finite
observable alphabet. This does not bound other train events. -/
theorem markedObservableEvent_bound
    (q v e : ℕ)
    (R : ℕ → Finset (ForestObservableAtom q v e))
    (active : ℕ → Prop) [DecidablePred active]
    (N : ℕ)
    (hMono : ∀ i : ℕ, i < N → R i ⊆ R (i + 1))
    (hActive :
      ∀ i : ℕ, i < N → active i → R i ⊂ R (i + 1)) :
    ((Finset.range N).filter active).card ≤
      (q * v) * (q * v) + q * e := by
  have h := activeRecordSteps_le R active N hMono hActive
  rw [forestObservableAtom_card] at h
  exact h

end StructuralRamsey.Girth
