import Girth.TrainActualChosenNonadjacentLongOldUncut
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: exact source-A2/A3 dichotomy for two contacts of one wagon

In a genuine acceptable BigCycle, suppose one actual wagon w
contains two DISTINCT vertex connector positions a,b (as witnessed
by physical incident edges). There are exactly two possibilities:

* w is FRESH among the source connectors. The original A3 window
  places a,b at consecutive cyclic source positions (in either
  orientation).
* w is an OLD source wagon connector at t. The original A2
  restricts a,b to pred(t),succ(t), in one of the two orientations.

This preserves the real labelled quotient wagon w; no arbitrary
carrier quotient, no selected reduced long plan, and no constructed
source replacement. It isolates exactly the finite physical geometry
needed to split the remaining two-cut nonedge/long transfer into
fresh-one-long and old-wagon-two-short cases. Circulation only.
-/

namespace StructuralRamsey.Girth.OrderOneData
universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A2/A3 classify two distinct actual vertex contacts with the
SAME physical wagon as either adjacent fresh contacts, or the
two opposite neighbors of an existing wagon connector. -/
theorem BigCycle.two_wagon_contacts_fresh_adjacent_or_old_straddle
    {n : ℕ} (K : D.BigCycle n)
    (hAccept : K.Acceptable)
    (w : P) (a b : Fin n)
    (hab : a ≠ b)
    (ha : K.InWagonAt w a)
    (hb : K.InWagonAt w b) :
    ((∀ t : Fin n, K.connector t ≠ Sum.inr w) ∧
      (b = cyclicSucc a ∨ a = cyclicSucc b)) ∨
    (∃ t : Fin n, K.connector t = Sum.inr w ∧
      ((a = trainCyclicPred t ∧ b = cyclicSucc t) ∨
       (a = cyclicSucc t ∧ b = trainCyclicPred t))) := by
  by_cases hOld : ∃ t : Fin n, K.connector t = Sum.inr w
  · right
    obtain ⟨t, ht⟩ := hOld
    exact ⟨t, ht,
      K.old_wagon_distinct_contacts_straddle
        D hAccept.2.1 w t a b ht ha hb hab⟩
  · left
    have hFresh : ∀ t : Fin n, K.connector t ≠ Sum.inr w := by
      intro t ht
      exact hOld ⟨t, ht⟩
    obtain ⟨root, hWindow⟩ := hAccept.2.2 w hFresh
    refine ⟨hFresh, ?_⟩
    rcases hWindow a ha with hAroot | hAnext
    · rcases hWindow b hb with hBroot | hBnext
      · exact False.elim (hab (hAroot.trans hBroot.symm))
      · left
        rw [hAroot, hBnext]
    · rcases hWindow b hb with hBroot | hBnext
      · right
        rw [hAnext, hBroot]
      · exact False.elim (hab (hAnext.trans hBnext.symm))

end StructuralRamsey.Girth.OrderOneData
