import Girth.TrainFillingPrivateOriginalImageInH
import Girth.TrainFillingIndexedContractedTrain

set_option Elab.async false

/-!
# Exact restored train wagons on original selected T edges

The original train T has a first-wagon partition, and its later
wagons are determined by the quotient of first-wagon labels P.
For the local first-wagon edge e belonging to F_p the inherited
restored wagon at level nu.succ is (choice c, [p]_nu).

A genuine parentwise realization R preserves and reflects these
quotient names, so two edges of the same selected original T-copy
have the same ambient wagon at that level IF AND ONLY IF their
original first-wagon parents were equivalent under T.rel nu.

Within a common selected parent, distinct EHN choices cannot
share a proper-wagon label. The universal top is deliberately
EXCLUDED from the tagged parent record and stays global.

This proves the literal selected EDGE-train relation, not the
existence of the original T relational/partite embedding. The
latter still requires equality of original physical edges,
predicates, within-part orders and the original train bookkeeping.

Source candidates until exact-head Lean kernel checking.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q GV GE I GQ : Type v}
variable (S : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (S c).toPrivateWagonInput

/-- An original first-wagon edge in component c receives its
actual tagged source proper-wagon name, no invented owner. -/
theorem selectedTaggedOriginalEdge_parent
    {m : ℕ} (T : EdgeTrainLevels P m)
    (ν : Fin (m + 1))
    (c : C) (e : (S c).OriginalEdge) :
    properParentOf (U S)
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
        (selectedTaggedOriginalEdge S c e) =
      (c, Quotient.mk (T.wagonSetoid ν) e.1) := rfl

/-- Within a single choice c, the SOURCE tagged parent equality
preserves and reflects the old train relation on the two original
first-wagon labels. -/
theorem selectedOriginalEdge_sourceWagon_iff
    {m : ℕ} (T : EdgeTrainLevels P m)
    (ν : Fin (m + 1)) (c : C)
    (e f : (S c).OriginalEdge) :
    T.rel ν e.1 f.1 ↔
      properParentOf (U S)
        (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
          (selectedTaggedOriginalEdge S c e) =
      properParentOf (U S)
        (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
          (selectedTaggedOriginalEdge S c f) := by
  rw [selectedTaggedOriginalEdge_parent S T ν c e,
      selectedTaggedOriginalEdge_parent S T ν c f]
  constructor
  · intro h
    exact congrArg (fun q : Quotient (T.wagonSetoid ν) => (c, q))
      (Quotient.sound h)
  · intro h
    exact Quotient.exact (congrArg Prod.snd h)

/-- The restored proper wagon of a selected original T-edge under
an ACTUAL parentwise realization is literally the image of the
source tagged first-wagon quotient. -/
theorem ParentwiseRealization.selectedOriginalEdge_parent
    {m : ℕ} (T : EdgeTrainLevels P m)
    (ν : Fin (m + 1))
    (D : OrderOneData GV GE I GQ)
    (R : ParentwiseRealization (U S)
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p) D)
    (i : I) (c : C) (e : (S c).OriginalEdge) :
    D.parent (R.edge i (selectedTaggedOriginalEdge S c e)) =
      R.wagon i (c, Quotient.mk (T.wagonSetoid ν) e.1) := by
  rw [R.parent_eq i (selectedTaggedOriginalEdge S c e)]
  rfl

/-- The ACTUAL H proper-wagon relation on original selected T
edges is precisely its source relation. This gives all positive
restored cuts by applying the theorem separately to each
nu<m. The inherited top does not need tagged names. -/
theorem ParentwiseRealization.selectedOriginalEdge_wagon_iff
    {m : ℕ} (T : EdgeTrainLevels P m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (D : OrderOneData GV GE I GQ)
    (R : ParentwiseRealization (U S)
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p) D)
    (i : I) (c : C) (e f : (S c).OriginalEdge) :
    T.rel ν e.1 f.1 ↔
      D.parent (R.edge i (selectedTaggedOriginalEdge S c e)) =
      D.parent (R.edge i (selectedTaggedOriginalEdge S c f)) := by
  rw [R.selectedOriginalEdge_parent S T ν D i c e,
      R.selectedOriginalEdge_parent S T ν D i c f]
  constructor
  · intro h
    exact congrArg (R.wagon i)
      ((selectedOriginalEdge_sourceWagon_iff S T ν c e f).mp h)
  · intro h
    exact (selectedOriginalEdge_sourceWagon_iff S T ν c e f).mpr
      ((R.wagon i).injective h)

/-- Distinct EHN choices under ONE selected old parent must have
different proper-wagon names, independently of whether different
old parents overlap elsewhere in N[X]. -/
theorem ParentwiseRealization.selectedOriginalEdge_wagon_ne_of_choice_ne
    {m : ℕ} (T : EdgeTrainLevels P m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (D : OrderOneData GV GE I GQ)
    (R : ParentwiseRealization (U S)
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p) D)
    (i : I) (c d : C) (hcd : c ≠ d)
    (e : (S c).OriginalEdge) (f : (S d).OriginalEdge) :
    D.parent (R.edge i (selectedTaggedOriginalEdge S c e)) ≠
      D.parent (R.edge i (selectedTaggedOriginalEdge S d f)) := by
  intro h
  have hTags : (c, Quotient.mk (T.wagonSetoid ν) e.1) =
      (d, Quotient.mk (T.wagonSetoid ν) f.1) := by
    apply (R.wagon i).injective
    simpa only [R.selectedOriginalEdge_parent S T ν D i c e,
       R.selectedOriginalEdge_parent S T ν D i d f] using h
  exact hcd (congrArg Prod.fst hTags)

end StructuralRamsey.Girth.IndexedPrivateChoice
