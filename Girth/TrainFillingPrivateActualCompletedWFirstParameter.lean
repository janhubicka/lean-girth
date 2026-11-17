import Girth.TrainFillingPrivateActualFirstParameter
import Girth.TrainFillingPrivateActualCompletedWMarked

set_option Elab.async false

/-!
# Completed W marking directly from the ORIGINAL first train parameter

The original T first parameter is precisely a
TrainParentIntersectionBound between equality-cut physical
edges and their first-wagon ancestors.

We compose that source theorem with the genuine owner map
and completed W's induced support decomposition.
Thus NO separate local intersection bound on each F_p
must be supplied to the completed-W owner-split input.

The completed ordered W is only the FIRST Ramsey target;
Track 1's covered/marked X witness and the shorter RR_h
selected OrderStage remain separate.

Uncompiled Lean source candidate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {I : Type u} {V : Type v}
variable [LinearOrder I] [LinearOrder V] [Finite V]

/-- The manuscript's original parameter A₁ directly bounds
intersections of EVERY pair of distinct small-A edges
in the COMPLETED ordered first-wagon union W.

The premise uses the ACTUAL original bottom-to-first-wagon
parent map, not an arbitrary owner or a property of
the proposed EHN output. -/
theorem actualFirstWagonCompletedW_marked_of_parentBound
    (k : ℕ) (hk : 2 ≤ k)
    (profile : Fin k → I)
    (oldEdges : Set (Set V)) (colour : V → I)
    {m : ℕ}
    (T : EdgeTrainLevels
      {e : Set V // e ∈ supportCopies
        (colouredOrderedEdgeSource.{u,v} k profile)
        (colouredOrderedEdgeTarget k oldEdges colour)} m)
    (μ : Fin (m + 1))
    (g : ℕ) (hg : 2 ≤ g)
    (hGirth : LabelledGirthGT
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)} => e.1)
        μ) g)
    (allowed : Set I)
    (hParameter : TrainParentIntersectionBound
      (T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)} => e.1)
        (0 : Fin (m + 1)))
      (T.wagonParent (0 : Fin (m + 1)) μ
        (by change (0 : Nat) ≤ μ.val; omega))
      {v : V | colour v ∈ allowed}) :
    let A := colouredOrderedEdgeSource.{u,v} k profile
    let D := colouredOrderedEdgeTarget k oldEdges colour
    let P := Quotient (T.wagonSetoid μ)
    let carrier : P → Set V :=
      T.wagonClassCarrier
        (fun e : {e : Set V // e ∈ supportCopies A D} => e.1) μ
    letI : LinearOrder P := T.wagonQuotientLinearOrder μ
    ∀ e f : Set (FirstWagonUnionVertex carrier),
      e ∈ supportCopies A
        (completedFirstWagonColouredUnion k oldEdges colour carrier) →
      f ∈ supportCopies A
        (completedFirstWagonColouredUnion k oldEdges colour carrier) →
      e ≠ f →
      e ∩ f ⊆ {z | colour z.2.1 ∈ allowed} := by
  exact actualFirstWagonCompletedW_support_inter_allowed
    k hk profile oldEdges colour T μ g hg hGirth allowed
    (fun e f hne hSame =>
      T.firstParameter_physicalEdge_inter_allowed
        (fun x : {e : Set V // e ∈ supportCopies
          (colouredOrderedEdgeSource.{u,v} k profile)
          (colouredOrderedEdgeTarget k oldEdges colour)} => x.1)
        μ {v : V | colour v ∈ allowed}
        hParameter e f hne hSame)

end StructuralRamsey.Girth
