import Girth.ForestObservableProfile
import Mathlib.Tactic

/-!
# Bounded number of genuinely observable agreement events

Fix q abstract B-copies and let B have v named vertices. Their
complete equality profile is determined by a relation on at most
(q*v)^2 ordered pairs of named vertex slots.

During a *monotone information record*, if each interesting event
reveals some previously unrecorded agreement of those slots, then
the number of interesting events is at most (q*v)^2, independently
of the length of the unobserved historical genealogy. This is about
knowledge becoming recorded, NOT about two distinct vertices of an
already embedded old structure later becoming equal.

The theorem is a finite potential argument. It does not show that
all actual successor events are such observable merges, or that
unobserved events can always be deleted by the free ancestral
one-gap maps. These are the still-open diary representation tasks.
-/

namespace StructuralRamsey.Girth

/-- Vertex slots in q abstract copies of a v-vertex template. -/
abbrev MarkedVertexSlot (q v : ℕ) := Fin q × Fin v

/-- Equality facts *recorded so far* at a history stage. A new
entry means disclosure of an old equality, not an identification of
vertices in an injective stage embedding. No equivalence axiom is
required for the elementary counting bound. -/
abbrev ObservedPairSet (q v : ℕ) :=
  Finset (MarkedVertexSlot q v × MarkedVertexSlot q v)

/-- If each of n interesting levels adds a genuinely new observed
pair and previously observed pairs remain observed, then n cannot
exceed the number of pairs of labelled vertices in the q-family. -/
theorem strictlyGrowingAgreementEvents_bounded
    (q v n : ℕ)
    (record : ℕ → ObservedPairSet q v)
    (hStrict : ∀ i : ℕ, i < n → record i ⊂ record (i + 1)) :
    n ≤ (q * v) * (q * v) := by
  classical
  have hLower :
      ∀ i : ℕ, i ≤ n → i ≤ (record i).card := by
    intro i
    induction i with
    | zero =>
        intro hi
        exact Nat.zero_le _
    | succ i ih =>
        intro hi
        have hismall : i < n := by omega
        have hCard :
            (record i).card < (record (i + 1)).card :=
          Finset.card_lt_card (hStrict i hismall)
        have hPrev : i ≤ (record i).card := ih (by omega)
        omega
  have hUpper :
      (record n).card ≤
        (Finset.univ :
          ObservedPairSet q v).card := by
    exact Finset.card_le_card (Finset.subset_univ _)
  have hCardUniv :
      (Finset.univ :
        ObservedPairSet q v).card =
      (q * v) * (q * v) := by
    simp [ObservedPairSet, MarkedVertexSlot,
      Fintype.card_prod]
  exact (hLower n le_rfl).trans
    (hUpper.trans_eq hCardUniv)

/-- The same bound when one marks a specified number of stages
as genuinely new observable equalities: no semantic information
about unmarked stages is needed for the numerical conclusion. -/
theorem observableDiaryEvents_bound
    (q v d : ℕ)
    (record : ℕ → ObservedPairSet q v)
    (hEvent : ∀ i < d, record i ⊂ record (i + 1)) :
    d ≤ (q * v) ^ 2 := by
  simpa [pow_two] using
    strictlyGrowingAgreementEvents_bounded q v d record
      (fun i hi => hEvent i hi)

end StructuralRamsey.Girth
