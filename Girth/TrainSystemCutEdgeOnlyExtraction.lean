import Girth.TrainRecursiveInitialTailSystem

/-!
# An acceptable edge-only cycle forces a short labelled wagon cycle

The circulation manuscript uses the forward edge-only/wagon-girth
correspondence at each cutoff q >= 2: an acceptable big cycle whose
every label is a genuine physical edge, with twice-order at most 2*q,
implies a labelled Berge cycle of wagons of length at most q.

The existing initial-tail incidence proof already supplied the exact
contradiction against labelled girth >q. Classical contraposition here
extracts a REAL labelled Berge cycle at the same order budget.
Neither equal wagon carriers nor duplicate ambient edge sets are
identified, and no temporary designated copy is introduced.

Together with the verified system-to-labelled-cut converse (#713),
this separates both directions of the manuscript's edge-only lemma.
The proof does not assert a completed recursive PictureStep.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Every acceptable physical edge-only big cycle of numerical order
at most q (q >= 2) has a labelled wagon Berge cycle of length at
most q, under the actual complete pretrain linearity condition. -/
theorem BigCycle.exists_labelledWagonCycle_of_acceptable_edgeOnly
    {n : ℕ} (C : D.BigCycle n)
    (hLinear : D.LinearPretrain)
    (hAccept : C.Acceptable)
    (hOnly : ∀ j : Fin n, ∃ e : E, C.label j = Sum.inr e)
    (q : ℕ) (hq : 2 ≤ q)
    (hOrder : C.twiceOrder ≤ 2 * q) :
    ∃ B : LabelledBergeCycle
        (fun p : P => {x : V | D.WagonVertex p x}),
      B.length ≤ q := by
  classical
  by_contra hNot
  have hCut : LabelledGirthGT
      (fun p : P => {x : V | D.WagonVertex p x}) q := hNot
  choose edge hLabel using hOnly
  exact C.false_of_edge_only_of_labelledCutGirth
    edge hLabel hLinear.1 hAccept q hq hCut hOrder

end StructuralRamsey.Girth.OrderOneData
