import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual inserted fine-train adjacent parameters from the chosen refinement

The q>2 lower target is the true active A-partite source. Its physical
train is refined while the OLD ambient part map P is pulled back to
the active A-part map via the processed embedding alpha : A ↪ P.

At an inserted parent j+1 the canonical fineAllowedFromRefinement
is exactly the preimage under alpha of the refinement's permitted
old P-part set. If oldPart x = alpha (activePart x), the corresponding
permitted VERTEX SET is LITERALLY the one in the genuine
FirstWagonRefinement.parameters field. We can therefore transfer
its complete parent-child sibling-intersection bound, without
assuming any fine adjacent parameter certificate externally.

This proves all INSERTED adjacent parent bounds (j=0,...,extraCuts),
including the first retained parent at extraCuts+1. It does NOT
derive the retained positive adjacent bounds above that parent,
the missing GLOBAL labelled girth at the first retained cut, or the
lower recursive witness and attached-output SupremeCycleBound.
No ambient A-support edges or wagon labels are removed; no appendix.
-/

namespace StructuralRamsey.Girth

open TrainRecursiveWitness

universe v
variable {E W UA P : Type v}
variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {oldPart : W → P}
variable {firstAllowed : Set P} {g : ℕ}

/-- At one actual inserted parent the canonical fine A-part allowed
set, pulled back to active vertices, is EXACTLY the original
refinement permitted vertex set in the old P-part coordinates. -/
theorem FirstWagonRefinement.canonicalFineAllowed_parent_preimage_eq
    (R : FirstWagonRefinement T hm edge oldPart firstAllowed g)
    (α : UA ↪ P) (activePart : W → UA)
    (hPart : ∀ x : W, oldPart x = α (activePart x))
    (oldAllowed : Fin (m + 1) → Set P)
    (j : Fin (R.extraCuts + 1)) :
    activePart ⁻¹'
      (fineAllowedFromRefinement m R.extraCuts hm
        α oldAllowed R.permitted
        (firstRefinementParent m R.extraCuts hm j)) =
    oldPart ⁻¹' R.permitted j := by
  rw [fineAllowedFromRefinement_parent
    m R.extraCuts hm α oldAllowed R.permitted j]
  ext x
  change α (activePart x) ∈ R.permitted j ↔
    oldPart x ∈ R.permitted j
  rw [hPart x]

/-- Every inserted fine-train adjacent parent bound is already stored
in the genuine FirstWagonRefinement; the active part-coordinate
pullback introduces no new geometric or combinatorial hypothesis. -/
theorem FirstWagonRefinement.canonicalInserted_adjacentParameter
    (R : FirstWagonRefinement T hm edge oldPart firstAllowed g)
    (α : UA ↪ P) (activePart : W → UA)
    (hPart : ∀ x : W, oldPart x = α (activePart x))
    (oldAllowed : Fin (m + 1) → Set P)
    (j : Fin (R.extraCuts + 1)) :
    TrainParentIntersectionBound
      (R.train.wagonClassCarrier edge
        (firstRefinementChild m R.extraCuts hm j))
      (R.train.wagonParent
        (firstRefinementChild m R.extraCuts hm j)
        (firstRefinementParent m R.extraCuts hm j)
        (by change j.val ≤ j.val + 1; omega))
      (activePart ⁻¹'
        (fineAllowedFromRefinement m R.extraCuts hm
          α oldAllowed R.permitted
          (firstRefinementParent m R.extraCuts hm j))) := by
  rw [R.canonicalFineAllowed_parent_preimage_eq
    α activePart hPart oldAllowed j]
  exact R.parameters j

end StructuralRamsey.Girth
