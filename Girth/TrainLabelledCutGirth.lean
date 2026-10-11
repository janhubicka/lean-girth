import Girth.TrainWagonClassRestriction
import Girth.LabelledWagonCutRestriction

/-!
# Labelled horizontal train girth under deleting uncovered edges

A covered-edge reduction of a train restricts edge labels and their
nested wagon equivalences, so each surviving wagon class injects
into its old one. The surviving wagon carrier is included in the
old carrier. Since the labelled Berge cycle obstruction remembers
wagon labels, no short cycle can be created at ANY level.

This is the complete abstract train horizontal-cut girth
preservation interface; actual edge-coverage pruning of local
Ramsey witnesses and the preservation of the more delicate
single-part refinement predicate are separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {E F W : Type v}

/-- Restricting the edge labels of a train and shrinking its physical
edge carriers cannot decrease the girth at any labelled wagon cut. -/
theorem EdgeTrainLevels.labelledCutGirth_restrict
    {m : ℕ} (T : EdgeTrainLevels E m)
    (oldEdges : E → Set W) (keep : F ↪ E)
    (newEdges : F → Set W)
    (hShrink : ∀ f : F, newEdges f ⊆ oldEdges (keep f))
    (μ : Fin (m + 1)) (q : ℕ)
    (hOld : LabelledGirthGT (T.wagonClassCarrier oldEdges μ) q) :
    LabelledGirthGT
      ((T.restrict keep).wagonClassCarrier newEdges μ) q := by
  exact labelledGirthGT_of_injective_shrinking
    (T.wagonClassCarrier oldEdges μ)
    ((T.restrict keep).wagonClassCarrier newEdges μ)
    (T.wagonClassEmbedding keep μ)
    (T.wagonClassEmbedding keep μ).injective
    (T.wagonClassCarrier_restrict_subset
      oldEdges keep newEdges hShrink μ)
    q hOld

end StructuralRamsey.Girth
