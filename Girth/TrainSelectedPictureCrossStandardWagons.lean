import Girth.TrainActualCopyLocalCoreIncidence
import Girth.TrainCoreWagonBridge
import Girth.TrainInteriorParentQuotientBridge
import Girth.TrainActualTopParentQuotientBridge
import Girth.TrainBigCycleTwoWagonObstruction

set_option Elab.async false

/-!
# A pair of distinct standards has at most one common output wagon

Each generated wagon containing physical support edges from two distinct
standards has a core ancestor with genuine shared edges in both prescribed
witness copies. The standard/core quotient bridge identifies the ancestor's
embedded class with the original output wagon, retaining its label.

Two distinct output wagons would therefore give two distinct core wagons
meeting both witness copies. The core local piece bound at order two excludes
exactly this configuration. Neither source nor output wagon linearity,
strongness, finite support, or a vertex-pair edge is required.

The hypotheses specify genuine physical edges of the two standards. This
theorem does not localize arbitrary output endpoint witnesses, and does not
claim the remaining cases of global output wagon linearity.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section CrossStandardWagons

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L Old) (S : Set Old) (R : RelStructure L Core)
variable (f : I → RelStructure.Embedding (B.induce S) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A B) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A B S))
variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A B S),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A B S R f k p)
      (sharedOldACarrierCoreEmbedding A B S R f k q))
variable (μ : Fin (m + 1))

local notation "Emb" => sharedOldACarrierCoreEmbedding A B S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A B S R f
local notation "Train" => generatedActualASupportTrain A hA B S R f T U hShared
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "StdEdge" => (fun (i : I) (a : OldACarrierEdge A B) =>
  actualAPictureEdgeEquiv A hA B S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A B S) Emb i a))
local notation "Parent" => Quotient.mk (EdgeTrainLevels.wagonSetoid
  (generatedActualASupportTrain A hA B S R f T U hShared) μ)

include hRel

/-- At a fixed train cut, two distinct standards cannot each contain physical
edges from two different generated output wagons. The core bound is only its
order-two necessary local consequence; no linearity or strongness is assumed. -/
theorem generatedActualASupportTrain_cross_standard_wagon_unique
    (hBound : (Witness).LocalPieceSystemBound 2)
    (i j : I) (hij : i ≠ j)
    (a b c d : OldACarrierEdge A B)
    (W₁ W₂ : Quotient ((Train).wagonSetoid μ))
    (ha : Parent (StdEdge i a) = W₁)
    (hb : Parent (StdEdge j b) = W₁)
    (hc : Parent (StdEdge i c) = W₂)
    (hd : Parent (StdEdge j d) = W₂) :
    W₁ = W₂ := by
  classical
  have hAB : (Train).rel μ (StdEdge i a) (StdEdge j b) :=
    Quotient.exact (s := (Train).wagonSetoid μ) (ha.trans hb.symm)
  have hCD : (Train).rel μ (StdEdge i c) (StdEdge j d) :=
    Quotient.exact (s := (Train).wagonSetoid μ) (hc.trans hd.symm)
  obtain ⟨p, s₁, t₁, hs₁, _ht₁, hsp, htp, _hsLocal, _htLocal⟩ :=
    generatedActualASupportTrain_cross_standard_copy_local_incidence
      A hA B S R f T U hShared hRel μ i j hij a b hAB
  obtain ⟨q, s₂, t₂, hs₂, _ht₂, hsq, htq, _hsLocal, _htLocal⟩ :=
    generatedActualASupportTrain_cross_standard_copy_local_incidence
      A hA B S R f T U hShared hRel μ i j hij c d hCD
  let κ : Quotient (U.wagonSetoid μ) ↪ Quotient ((Train).wagonSetoid μ) :=
    generatedActualASupportTrain_coreWagonEmbedding
      A hA B S R f T U
      (fun ν k s t h => (hRel ν k s t).mp h) hShared μ
  have hW₁ : W₁ = κ p := by
    calc
      W₁ = κ (Quotient.mk (U.wagonSetoid μ) (Emb i s₁)) :=
        generatedActualASupportTrain_standard_parent_eq_coreEmbedding
          A hA B S R f T U hShared hRel μ i a s₁ W₁ ha hs₁
      _ = κ p := congrArg (fun w => κ w) hsp
  have hW₂ : W₂ = κ q := by
    calc
      W₂ = κ (Quotient.mk (U.wagonSetoid μ) (Emb i s₂)) :=
        generatedActualASupportTrain_standard_parent_eq_coreEmbedding
          A hA B S R f T U hShared hRel μ i c s₂ W₂ hc hs₂
      _ = κ q := congrArg (fun w => κ w) hsq
  by_contra hNe
  have hpq : p ≠ q := by
    intro hEq
    exact hNe (hW₁.trans ((congrArg (fun w => κ w) hEq).trans hW₂.symm))
  exact OrderOneData.no_two_designated_meet_two_wagons
    Witness hBound i j p q hij hpq
    ⟨Emb i s₁, ⟨s₁, rfl⟩, hsp⟩
    ⟨Emb i s₂, ⟨s₂, rfl⟩, hsq⟩
    ⟨Emb j t₁, ⟨t₁, rfl⟩, htp⟩
    ⟨Emb j t₂, ⟨t₂, rfl⟩, htq⟩

end CrossStandardWagons

end StructuralRamsey.Girth
