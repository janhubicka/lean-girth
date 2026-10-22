import Girth.TrainCoreContactReflection
import Girth.TrainCyclicRestriction

/-!
# Actual witness-core maps satisfy the conditional cyclic restriction interface

The old cyclic restriction lemma deliberately takes geometric contact and
pair-edge reflection as hypotheses. For the *actual* generated attached
picture, these fields follow from actual core-edge carriers and the injective
core wagon-class map, without imposing a fictitious output-side edge map.

Only the existence of a legal target word and its exact connector identity
is assumed. These inputs are NOT established by this theorem: selected
target-label incidence and the order-one designated-label A1 case remain
separate parts of the physical cut-indexed reduct.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualCoreRestrictionMap

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
variable (hPreserve : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 →
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U hPreserve hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : OldACarrierEdge A R → Set Y)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

/-- The two semantic hypotheses of cyclic restriction are automatic
for actual core inclusion and genuine core-to-output wagon embedding.
Thus any legal target big cycle with correctly transported connectors
supplies an actual RestrictionMap. No label or cycle-transfer conclusion
is added by the statement. -/
theorem attachedSelectedPicture_core_restrictionMap
    {n k : ℕ}
    (K : (Out).BigCycle n) (Z : (Wit).BigCycle k)
    (position : Fin k ↪o Fin n)
    (hConnector : ∀ j : Fin k,
      K.connector (position j) =
        Sum.map CoreEmb CoreWagon (Z.connector j)) :
    K.RestrictionMap Z := by
  refine {
    position := position
    vertex := CoreEmb
    wagon := CoreWagon
    vertex_injective := CoreEmb.injective
    wagon_injective := CoreWagon.injective
    connector_eq := hConnector
    contact := ?_
    pair_reflect := ?_
  }
  · intro p j x _ hContact
    exact attachedSelectedPicture_core_wagonContact_reflect
      A hA B D C family selected e R f T U hShared hPreserve μ
      p x hContact
  · intro j p x y _ _ _ _ _ _ hPair
    exact attachedSelectedPicture_core_pairEdge_reflect
      A hA B D C family selected e R f T U hShared μ
      x y hPair

end ActualCoreRestrictionMap
end StructuralRamsey.Girth
