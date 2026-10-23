import Girth.TrainActualCutIndexedBigCycle

/-!
# Acceptability of actual cyclic cut restrictions away from order one

The physical picture-step cut word now exists as a legal BigCycle and
its exact geometric RestrictionMap transfers A2 and A3. The only A1
requirement is numerical order one. Hence an actual cut word of order
at least two is acceptable whenever the source is acceptable,
without any designated-label provenance or global cycle-transfer input.

The order-one case must be handled separately by bridges. No claim is
made that an edge-only order-one word is acceptable.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v w
variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P} {D' : OrderOneData V' E' I' P'}

/-- A genuine cyclic restriction cannot lose acceptability except
possibly through the designated-label axiom at order one. -/
theorem BigCycle.RestrictionMap.acceptable_of_twiceOrder_ne_two
    {n m : ℕ} {C : D.BigCycle n} {B : D'.BigCycle m}
    (R : C.RestrictionMap B)
    (hAccept : C.Acceptable)
    (hNotOne : B.twiceOrder ≠ 2) :
    B.Acceptable :=
  R.acceptable hAccept (fun heq => False.elim (hNotOne heq))

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section CutAcceptableAboveOne

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))
local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- At every real cut assignment, if the reduced word has numerical
order at least two, actual acceptability (A1--A3) transfers.
The only hypotheses are those of the physical cut reduction. -/
theorem attachedSelectedPicture_geometric_cut_acceptable_of_two_le
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hAccept : K.Acceptable)
    (hOrder :
      4 ≤ (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).twiceOrder) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).Acceptable := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hNotOne : Z.twiceOrder ≠ 2 := by
    omega
  exact (attachedSelectedPicture_geometric_cut_restrictionMap
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts).acceptable_of_twiceOrder_ne_two
      hAccept hNotOne

end CutAcceptableAboveOne
end StructuralRamsey.Girth
