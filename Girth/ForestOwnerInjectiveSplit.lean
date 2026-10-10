import Girth.ForestUsedOwners
import Mathlib.Data.Fintype.EquivFin

/-!
# Repeated versus distinct standard-picture owners

The direct circulation forest increment has only two cases:
either all selected members have different containing standard
pictures, or two share one. In the latter case there are STRICTLY
fewer used owners than selected pieces. Hence under a size-q
budget their distinct containing pieces number at most q-1.

This establishes the entire combinatorial budget step, without
assuming finiteness of the full ambient owner index type.
The join-tree lifting step still has its separate geometric
and local-forest hypotheses.
-/

namespace StructuralRamsey.Girth

universe v
variable {N Q : Type v}

/-- A repeated owner strictly reduces the number of distinct
actually used standard-picture owners. -/
theorem usedOwner_card_lt_of_not_injective
    [Fintype N] (owner : N → Q)
    (hNoninj : ¬ Function.Injective owner) :
    letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
    Fintype.card (UsedOwner owner) < Fintype.card N := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  have hMapNoninj : ¬ Function.Injective (usedOwnerMap owner) := by
    intro hMapInj
    apply hNoninj
    intro a b hab
    apply hMapInj
    exact Subtype.ext hab
  exact Fintype.card_lt_of_surjective_not_injective
    (usedOwnerMap owner) (usedOwnerMap_surjective owner) hMapNoninj

/-- If some two selected members have the same owner, at most
q-1 distinct standard pictures are involved in a size-q family. -/
theorem usedOwner_card_le_prev_of_not_injective
    [Fintype N] (owner : N → Q)
    (q : ℕ) (hSize : Fintype.card N ≤ q)
    (hNoninj : ¬ Function.Injective owner) :
    letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
    Fintype.card (UsedOwner owner) ≤ q - 1 := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  have hlt := usedOwner_card_lt_of_not_injective owner hNoninj
  omega

/-- Exhaustive and disjointly motivated forest-increment split:
either every selected piece has its own owner, or the usable
local-owner set fits the preceding q-1 forest bound. -/
theorem owner_injective_or_usedOwner_card_le_prev
    [Fintype N] (owner : N → Q)
    (q : ℕ) (hSize : Fintype.card N ≤ q) :
    letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
    Function.Injective owner ∨
      Fintype.card (UsedOwner owner) ≤ q - 1 := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  by_cases hInjective : Function.Injective owner
  · exact Or.inl hInjective
  · exact Or.inr
      (usedOwner_card_le_prev_of_not_injective
        owner q hSize hInjective)

end StructuralRamsey.Girth
