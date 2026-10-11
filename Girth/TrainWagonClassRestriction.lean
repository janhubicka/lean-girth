import Girth.TrainEquivalenceRestriction
import Mathlib.Data.Quot

/-!
# Surviving wagon classes embed into original wagon classes

The restriction of train edge-equivalence levels is not allowed to
merge two different wagons. A surviving μ-wagon is precisely the
intersection of one OLD μ-equivalence class with the surviving edge
labels. Therefore each surviving class has a unique old ancestor
class, and distinct surviving classes have distinct old ancestors.

This is the missing quotient/parent-label interface needed to apply
labelled Berge girth monotonicity under deleting uncovered edges.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

/-- The setoid whose classes are the μ-wagons of the edge train. -/
def EdgeTrainLevels.wagonSetoid
    {m : ℕ} (T : EdgeTrainLevels E m)
    (μ : Fin (m + 1)) : Setoid E where
  r := T.rel μ
  iseqv := T.equivalent μ

/-- A surviving μ-wagon maps to its ORIGINAL μ-wagon, and this
map is injective. In particular, repeated carrier sets are not
collapsed merely because they happen to have the same vertices. -/
def EdgeTrainLevels.wagonClassEmbedding
    {m : ℕ} (T : EdgeTrainLevels E m)
    (keep : F ↪ E) (μ : Fin (m + 1)) :
    Quotient ((T.restrict keep).wagonSetoid μ) ↪
      Quotient (T.wagonSetoid μ) := by
  let map : Quotient ((T.restrict keep).wagonSetoid μ) →
      Quotient (T.wagonSetoid μ) :=
    fun c => Quotient.liftOn c
      (fun a : F => Quotient.mk (T.wagonSetoid μ) (keep a))
      (by
        intro a b hab
        exact Quotient.sound hab)
  refine ⟨map, ?_⟩
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
          change
            (Quotient.mk (T.wagonSetoid μ) (keep a)) =
              Quotient.mk (T.wagonSetoid μ) (keep b) at hxy
          have hOldRel : T.rel μ (keep a) (keep b) :=
            Quotient.exact hxy
          exact Quotient.sound hOldRel

/-- Equivalent wagon representatives determine the same carrier. -/
theorem EdgeTrainLevels.wagonCarrier_eq_of_rel
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edges : E → Set W) (μ : Fin (m + 1))
    {a b : E} (hab : T.rel μ a b) :
    T.wagonCarrier edges μ a = T.wagonCarrier edges μ b := by
  ext x
  constructor
  · rintro ⟨c, hac, hxc⟩
    exact ⟨c, (T.equivalent μ).trans
      ((T.equivalent μ).symm hab) hac, hxc⟩
  · rintro ⟨c, hbc, hxc⟩
    exact ⟨c, (T.equivalent μ).trans hab hbc, hxc⟩

/-- The vertex carrier of a wagon, well defined on the QUOTIENT of
edge labels by the relevant train equivalence. -/
def EdgeTrainLevels.wagonClassCarrier
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edges : E → Set W) (μ : Fin (m + 1)) :
    Quotient (T.wagonSetoid μ) → Set W :=
  fun c => Quotient.liftOn c
    (fun a => T.wagonCarrier edges μ a)
    (by
      intro a b hab
      exact T.wagonCarrier_eq_of_rel edges μ hab)

/-- At every level and every surviving WAGON LABEL, its new carrier
is contained in the old carrier of the INJECTIVELY mapped old wagon. -/
theorem EdgeTrainLevels.wagonClassCarrier_restrict_subset
    {m : ℕ} (T : EdgeTrainLevels E m)
    (oldEdges : E → Set W) (keep : F ↪ E)
    (newEdges : F → Set W)
    (hShrink : ∀ f : F, newEdges f ⊆ oldEdges (keep f))
    (μ : Fin (m + 1)) :
    ∀ c : Quotient ((T.restrict keep).wagonSetoid μ),
      (T.restrict keep).wagonClassCarrier newEdges μ c ⊆
        T.wagonClassCarrier oldEdges μ
          (T.wagonClassEmbedding keep μ c) := by
  intro c
  induction c using Quotient.inductionOn with
  | h a =>
      change
        (T.restrict keep).wagonCarrier newEdges μ a ⊆
          T.wagonCarrier oldEdges μ (keep a)
      exact T.wagonCarrier_restrict_subset
        oldEdges keep newEdges hShrink μ a

end StructuralRamsey.Girth
