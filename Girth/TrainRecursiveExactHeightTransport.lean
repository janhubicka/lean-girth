import Girth.TrainLabelledCutGirth
import Girth.TrainAllAdjacentParameterPreservation

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact arithmetic transport of train height

The q>2 lower cutoff vector has length
  (replicate (extraCuts+1) (q-1) ++ tail).length,
while the actual FirstWagonRefinement train uses
  (q :: tail).length + extraCuts.
These natural numbers are provably equal but are not necessarily
definitionally equal. The actual edge labels, equivalence relations,
physical carriers, and wagon-parent maps must not be replaced or
reconstructed merely to change the type index.

This is pure equality transport of the SAME train. It carries
all labelled horizontal girth certificates and all adjacent-parent
intersection parameters, with the Fin coordinate cast made explicit.
No new combinatorial or girth assumption is introduced.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W : Type v}

/-- Change only the natural-number index of a train along a proof of
equality of heights. This neither creates nor removes physical edges. -/
def EdgeTrainLevels.castHeight
    {m n : ℕ} (T : EdgeTrainLevels E m) (h : m = n) :
    EdgeTrainLevels E n := by
  cases h
  exact T

@[simp] theorem EdgeTrainLevels.castHeight_rfl
    {m : ℕ} (T : EdgeTrainLevels E m) :
    T.castHeight rfl = T := rfl

/-- Labelled cut girth at a coordinate survives exact height
reindexing, with the actual quotient wagon family unchanged. -/
theorem EdgeTrainLevels.castHeight_labelledCutGirth
    {m n : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (h : m = n)
    (ρ : Fin (n + 1)) (q : ℕ)
    (hOld : LabelledGirthGT
      (T.wagonClassCarrier edge
        (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ρ)) q) :
    LabelledGirthGT ((T.castHeight h).wagonClassCarrier edge ρ) q := by
  cases h
  exact hOld

/-- Every adjacent sibling-intersection parameter survives the SAME
height reindexing; only its Fin argument is cast along equality. -/
theorem EdgeTrainLevels.castHeight_adjacentParameters
    {m n : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (h : m = n)
    (allowed : Fin (m + 1) → Set W)
    (hOld : T.AdjacentParameters edge allowed) :
    (T.castHeight h).AdjacentParameters edge
      (fun ρ => allowed
        (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ρ)) := by
  cases h
  exact hOld

end StructuralRamsey.Girth
