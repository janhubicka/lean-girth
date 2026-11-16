import Girth.TrainFillingPrivateActualSourceEdgeEquiv
import Girth.TrainFillingPrivateActualChoiceTrain

set_option Elab.async false

/-!
# Owner-faithful equivalence for the actual first-wagon source

This follows the original train's genuine first-wagon quotient, not an
independently chosen owner map. The existing actualSourceEdgeEquiv gives
the bijection; its inverse preserves the original first-wagon label
because the forward map has the correct owner by construction.

This is a local source-level bridge. Identifying these induced local
edges with the *specific* EHN SummandPrivateTemplate.OriginalEdge,
and combining the resulting map with one selected H embedding, remain
separate application obligations.

No new axioms, admissions, or output-girth hypothesis.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V : Type v}

/-- The original train's physical edge has precisely the first-wagon
owner of its inverse image in the dependent family of induced wagons.
This is stronger than an abstract equivalence of finite edge sets. -/
theorem EdgeTrainLevels.actualSourceEdgeEquiv_symm_owner
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ) g)
    (e : {e : Set V // e ∈ supportCopies A D}) :
    (T.actualSourceEdgeEquiv A D μ g hg hGirth).symm e |>.1 =
      T.wagonClassOwner μ e := by
  let carrier :=
    T.wagonClassCarrier
      (fun f : {f : Set V // f ∈ supportCopies A D} => f.1) μ
  let owner := T.wagonClassOwner μ
  have hLinear :
      ∀ p q : Quotient (T.wagonSetoid μ), p ≠ q →
        (carrier p ∩ carrier q).Subsingleton :=
    (T.actualWagon_EHN_source_of_bound A D μ g hg hGirth).1
  have hCarrier :
      ∀ f : {f : Set V // f ∈ supportCopies A D},
        f.1 ⊆ carrier (owner f) := by
    intro f
    exact T.edge_subset_ownerWagonCarrier
      (fun z : {z : Set V // z ∈ supportCopies A D} => z.1) μ f
  have hOwner :=
    firstWagonEdgeToOriginal_owner A D carrier owner
      hCarrier hLinear
      ((T.actualSourceEdgeEquiv A D μ g hg hGirth).symm e)
  have hForward :
      firstWagonEdgeToOriginal A D carrier
        ((T.actualSourceEdgeEquiv A D μ g hg hGirth).symm e) = e := by
    exact (T.actualSourceEdgeEquiv A D μ g hg hGirth).apply_symm_apply e
  exact hOwner.symm.trans (congrArg owner hForward)

/-- An owner-preserving source equivalence is already sufficient to
transport the true tail-quotient relation: no new first-wagon train
relation is supplied to the cutoff-two argument. -/
theorem EdgeTrainLevels.actualSourceEdgeEquiv_tail_rel
    [Nontrivial UA]
    (A : RelStructure L UA) (D : RelStructure L V)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies A D} (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1)
        (EdgeTrainLevels.firstWagonLevel m)) g)
    (ν : Fin (m + 1))
    (e f : {e : Set V // e ∈ supportCopies A D}) :
    (T.tailQuotient).rel ν
      ((T.actualSourceEdgeEquiv A D
          (EdgeTrainLevels.firstWagonLevel m) g hg hGirth).symm e).1
      ((T.actualSourceEdgeEquiv A D
          (EdgeTrainLevels.firstWagonLevel m) g hg hGirth).symm f).1
      ↔ T.rel ν.succ e f := by
  have he := T.actualSourceEdgeEquiv_symm_owner A D
    (EdgeTrainLevels.firstWagonLevel m) g hg hGirth e
  have hf := T.actualSourceEdgeEquiv_symm_owner A D
    (EdgeTrainLevels.firstWagonLevel m) g hg hGirth f
  rw [he, hf]
  exact T.tailQuotient_rel_mk_iff ν e f

end StructuralRamsey.Girth
