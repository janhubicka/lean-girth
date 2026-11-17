import Girth.TrainAllAdjacentParameterPreservation
import Girth.TrainSimultaneousSupreme
import Girth.ForestMixedSetBound
import Girth.ForestOneEdgeOwnerLocalTest

set_option autoImplicit false

namespace StructuralRamsey.Girth

universe v
variable {V I : Type v} {m : ℕ}

namespace EdgeTrainLevels

/-- An incidence record on the complete labelled support edge family. -/
def carrierCutData {S : Set (Set V)} (T : EdgeTrainLevels {s // s ∈ S} m)
    (selected : I → Set V) (μ : Fin (m + 1)) :
    OrderOneData V {s // s ∈ S} I (Quotient (T.wagonSetoid μ)) where
  edgeCarrier := Subtype.val
  copyCarrier := selected
  copyEdges := fun i => {s | s.1 ⊆ selected i}
  parent := Quotient.mk (T.wagonSetoid μ)

/-- Carry a train to a literal equality of physical edge families. This
operation preserves the carrier and all quotient-label data. -/
def transportCarrierFamily {S R : Set (Set V)} (h : S = R)
    (T : EdgeTrainLevels {s // s ∈ S} m) : EdgeTrainLevels {s // s ∈ R} m :=
  h ▸ T

theorem transportCarrierFamily_rel {S R : Set (Set V)} (h : S = R)
    (T : EdgeTrainLevels {s // s ∈ S} m) (μ : Fin (m + 1))
    (a b : {s // s ∈ S}) :
    (T.transportCarrierFamily h).rel μ (⟨a.1, h ▸ a.2⟩ : {s // s ∈ R})
      ⟨b.1, h ▸ b.2⟩ ↔ T.rel μ a b := by
  cases h
  rfl

theorem transportCarrierFamily_adjacentParameters {S R : Set (Set V)} (h : S = R)
    (T : EdgeTrainLevels {s // s ∈ S} m) (allowed : Fin (m + 1) → Set V) :
    (T.transportCarrierFamily h).AdjacentParameters Subtype.val allowed ↔
      T.AdjacentParameters Subtype.val allowed := by
  cases h
  rfl

theorem transportCarrierFamily_fullSystemGirthGT {S R : Set (Set V)} (h : S = R)
    (T : EdgeTrainLevels {s // s ∈ S} m) (selected : I → Set V)
    (μ : Fin (m + 1)) (g : ℕ) :
    ((T.transportCarrierFamily h).carrierCutData selected μ).FullSystemGirthGT g ↔
      (T.carrierCutData selected μ).FullSystemGirthGT g := by
  cases h
  rfl

end EdgeTrainLevels

/-- This is the raw cutoff-two predecessor hypothesis on the genuine
mixed support family. It requires no forest claim at cutoff two itself. -/
theorem finiteMixedForestThrough_one (tested : HypergraphPiece V → Prop) :
    FiniteMixedForestThrough tested 1 := by
  intro s _hTest hCard
  haveI : Subsingleton {j : HypergraphPiece V // j ∈ s} :=
    Fintype.card_le_one_iff_subsingleton.mp (by simpa using hCard)
  exact forestOfCopies_of_subsingleton _

end StructuralRamsey.Girth
