import Girth.TrainFillingPrivateActualTailQuotient
import Girth.TrainFillingIndexedContractedTrain

set_option Elab.async false

/-!
# Actual choice-component train from the ORIGINAL quotient tail

At cutoff two, the first-wagon train given to the
heterogeneous contracted M is exactly the tailQuotient
of the ORIGINAL T, not an independently invented T'.

For original A-support edges a,b, the old first-wagon
labels are [a]_1 and [b]_1. Inside the SAME EHN choice
c, the contracted new nu-relation holds precisely
when the old (nu+1)-relation holds. Two DIFFERENT
EHN choices cannot share a proper contracted wagon.
The universal top is shared by ALL choices.

These results eliminate a separate truncated-train
relation hypothesis before invoking RR_h. All
vertex carriers, source partite parameters and
girth are handled in separate preparatory lemmas.

Candidate source; exact-head Lean/axiom check pending.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V X E : Type v}

/-- A genuine first-wagon label of the original train,
without collapsing distinct physical edge labels. -/
def actualFirstWagonLabel
    {m : ℕ} (Told : EdgeTrainLevels E (m + 1))
    (a : E) : Told.FirstWagon :=
  Quotient.mk
    (Told.wagonSetoid (EdgeTrainLevels.firstWagonLevel m)) a

/-- The actual heterogeneous contracted train relation
within one EHN choice is exactly the shifted ORIGINAL
train relation on old physical edge representatives,
for EVERY level including the universal top. -/
theorem actualContractedChoiceTrain_rel_original_iff
    {m : ℕ} (Told : EdgeTrainLevels E (m + 1))
    (hm : 0 < m)
    (U : C → PrivateWagonInput V Told.FirstWagon X)
    (c : C) (ν : Fin (m + 1)) (a b : E) :
    (contractedChoiceTrain U Told.tailQuotient hm).rel ν
      (c, actualFirstWagonLabel Told a)
      (c, actualFirstWagonLabel Told b) ↔
    Told.rel ν.succ a b := by
  change (ν.val = m ∨ (c = c ∧
    (Told.tailQuotient).rel ν
      (actualFirstWagonLabel Told a)
      (actualFirstWagonLabel Told b))) ↔
      Told.rel ν.succ a b
  constructor
  · rintro (hTop | ⟨_, hRel⟩)
    · have hIndex :
          ν = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) :=
        Fin.ext hTop
      rw [hIndex]
      exact Told.top a b
    · exact (Told.tailQuotient_rel_mk_iff ν a b).mp hRel
  · intro h
    exact Or.inr ⟨rfl,
      (Told.tailQuotient_rel_mk_iff ν a b).mpr h⟩

/-- Different EHN choice components remain entirely
separate at EVERY PROPER shortened train cut. This
is the actual sibling-separation fact, not a claim
that different selected old parents in N are disjoint. -/
theorem actualContractedChoiceTrain_rel_false_of_choice_ne
    {m : ℕ} (Told : EdgeTrainLevels E (m + 1))
    (hm : 0 < m)
    (U : C → PrivateWagonInput V Told.FirstWagon X)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (c d : C) (hcd : c ≠ d)
    (p q : Told.FirstWagon) :
    ¬ (contractedChoiceTrain U Told.tailQuotient hm).rel ν
        (c, p) (d, q) := by
  change ¬ (ν.val = m ∨
    (c = d ∧ (Told.tailQuotient).rel ν p q))
  rintro (hTop | ⟨hEq, _⟩)
  · exact (Nat.ne_of_lt hProper) hTop
  · exact hcd hEq

/-- The ONE universal top of the heterogeneous M joins
all first-wagon classes of all EHN choices; it is not
a separate top label for each component. -/
theorem actualContractedChoiceTrain_top_shared
    {m : ℕ} (Told : EdgeTrainLevels E (m + 1))
    (hm : 0 < m)
    (U : C → PrivateWagonInput V Told.FirstWagon X)
    (c d : C) (p q : Told.FirstWagon) :
    (contractedChoiceTrain U Told.tailQuotient hm).rel
      ⟨m, Nat.lt_succ_self m⟩ (c, p) (d, q) := by
  exact (contractedChoiceTrain U Told.tailQuotient hm).top (c, p) (d, q)

end StructuralRamsey.Girth.IndexedPrivateChoice
