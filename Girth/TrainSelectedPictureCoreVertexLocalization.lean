import Girth.TrainActualCopyLocalCoreIncidence
import Girth.TrainCoreWagonBridge
import Girth.TrainActualTwoStandardDesignatedBlock
import Girth.TrainActualPhysicalEdgeCarrierEval

set_option Elab.async false

/-!
# Same-parent core incidence at a vertex with two standard sources

Suppose two actual standard edges have the same generated wagon parent and
contain the same vertex, with distinct standard indices. The vertex lies in
the core, and active support coverage puts it in both prescribed shared
witness copies. The cross-standard quotient theorem supplies one core wagon
met by both copies. The witness order-one bound then gives shared edges of
that wagon through the vertex in both copies.

Shared train reflection recovers the original old wagon classes, and the
physical standard/core quotient bridge retains the original output parent.
Thus the conclusion gives actual core-edge incidence at exactly that vertex
and in exactly that output wagon. No source or output linearity, strongness,
or finite-type hypothesis is used.

Both source edges must contain the specified vertex. A wagon merely meeting
another standard elsewhere does not supply this two-source hypothesis, and
no unconditional localization of a single-source core vertex is asserted.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section CoreVertexLocalization

variable {L : RelLanguage.{u}} {UA P Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (C : StructuralRamsey.Partite.System L P Old) (α : UA → P)
variable (R : RelStructure L Core)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C α)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C α)))
variable (hRel : ∀ (ν : Fin (m + 1)) (k : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure (activeCarrier A C α)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C α) R f k p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C α) R f k q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C α
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Core) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : OldACarrierEdge A R) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Parent" => Quotient.mk (EdgeTrainLevels.wagonSetoid
  (generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared) μ)

include hRel

/-- A common wagon incident at one vertex through two distinct standards has
genuine shared representatives through that vertex in both standards. Their
old classes and the parent of their actual core images are retained. -/
theorem generatedActualASupportTrain_two_standard_vertex_shared_witnesses
    (hBound : (Witness).Bound)
    (i j : I) (hij : i ≠ j) (a b : OldEdge)
    (W : Quotient ((Train).wagonSetoid μ)) (x : Vertex)
    (ha : Parent (StdEdge i a) = W) (hb : Parent (StdEdge j b) = W)
    (hxa : x ∈ (StdEdge i a).1) (hxb : x ∈ (StdEdge j b).1) :
    ∃ s t : SharedEdge,
      T.rel μ s.1 a ∧ T.rel μ t.1 b ∧
      Parent (CoreActual (Emb i s)) = W ∧
      Parent (CoreActual (Emb j t)) = W ∧
      x ∈ CoreCar (Emb i s) ∧ x ∈ CoreCar (Emb j t) := by
  have standard_mem (k : I) (r : OldEdge) (hxr : x ∈ (StdEdge k r).1) :
      x ∈ copyCarrier (Std k) := by
    have hImage : x ∈ (fun z : Old => Std k z) '' r.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => x ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier
          A hA C.toRelStructure S R f k r)) hxr
    obtain ⟨z, _hz, hzx⟩ := hImage
    exact ⟨z, hzx⟩
  have hxi : x ∈ copyCarrier (Std i) := standard_mem i a hxa
  have hxj : x ∈ copyCarrier (Std j) := standard_mem j b hxb
  have hxCore : x ∈ copyCarrier CoreEmb :=
    attachment_copy_copy_intersection_subset_core C.toRelStructure S R f hij ⟨hxi, hxj⟩
  have hxiWitness : x ∈ (Witness).copyCarrier i :=
    activeAttached_mem_sharedWitness_of_standard_core A C α R f U μ i x hxi hxCore
  have hxjWitness : x ∈ (Witness).copyCarrier j :=
    activeAttached_mem_sharedWitness_of_standard_core A C α R f U μ j x hxj hxCore
  have hSame : (Train).rel μ (StdEdge i a) (StdEdge j b) :=
    Quotient.exact (s := (Train).wagonSetoid μ) (ha.trans hb.symm)
  obtain ⟨p, s₀, t₀, hs₀Old, ht₀Old, hs₀p, ht₀p, _hsLocal, _htLocal⟩ :=
    generatedActualASupportTrain_cross_standard_copy_local_incidence
      A hA C.toRelStructure S R f T U hShared hRel μ i j hij a b hSame
  have hDistinct : (Sum.inl i : I ⊕ OldACarrierEdge A R) ≠ Sum.inl j := by
    intro h
    exact hij (Sum.inl.inj h)
  obtain ⟨hBridgeI, hBridgeJ⟩ := OrderOneData.both_bridges
    Witness hBound (.inl i) (.inl j) x p hDistinct hxiWitness hxjWitness
    ⟨Emb i s₀, ⟨s₀, rfl⟩, hs₀p⟩
    ⟨Emb j t₀, ⟨t₀, rfl⟩, ht₀p⟩
  obtain ⟨r, hr, hrp, hxr⟩ := hBridgeI
  obtain ⟨q, hq, hqp, hxq⟩ := hBridgeJ
  change r ∈ Set.range (Emb i) at hr
  change q ∈ Set.range (Emb j) at hq
  obtain ⟨s, hs⟩ := hr
  obtain ⟨t, ht⟩ := hq
  have hsp : Quotient.mk (U.wagonSetoid μ) (Emb i s) = p :=
    (congrArg (Quotient.mk (U.wagonSetoid μ)) hs).trans hrp
  have htp : Quotient.mk (U.wagonSetoid μ) (Emb j t) = p :=
    (congrArg (Quotient.mk (U.wagonSetoid μ)) ht).trans hqp
  have hxs : x ∈ CoreCar (Emb i s) :=
    Eq.mpr (congrArg (fun r : OldACarrierEdge A R => x ∈ CoreCar r) hs) hxr
  have hxt : x ∈ CoreCar (Emb j t) :=
    Eq.mpr (congrArg (fun r : OldACarrierEdge A R => x ∈ CoreCar r) ht) hxq
  have hsCore : U.rel μ (Emb i s) (Emb i s₀) :=
    Quotient.exact (s := U.wagonSetoid μ) (hsp.trans hs₀p.symm)
  have htCore : U.rel μ (Emb j t) (Emb j t₀) :=
    Quotient.exact (s := U.wagonSetoid μ) (htp.trans ht₀p.symm)
  have hsOld : T.rel μ s.1 a :=
    (T.equivalent μ).trans ((hRel μ i s s₀).mpr hsCore) hs₀Old
  have htOld : T.rel μ t.1 b :=
    (T.equivalent μ).trans ((hRel μ j t t₀).mpr htCore) ht₀Old
  have hsW : Parent (CoreActual (Emb i s)) = W :=
    (generatedActualASupportTrain_standard_shared_wagon_eq
      A hA C.toRelStructure S R f T U hShared hRel μ i a s hsOld).symm.trans ha
  have htW : Parent (CoreActual (Emb j t)) = W :=
    (generatedActualASupportTrain_standard_shared_wagon_eq
      A hA C.toRelStructure S R f T U hShared hRel μ j b t htOld).symm.trans hb
  exact ⟨s, t, hsOld, htOld, hsW, htW, hxs, hxt⟩

/-- The same two-source incidence gives one genuine core support edge whose
actual output image contains the specified vertex and has the specified
generated wagon parent. -/
theorem generatedActualASupportTrain_two_standard_vertex_core_edge
    (hBound : (Witness).Bound)
    (i j : I) (hij : i ≠ j) (a b : OldEdge)
    (W : Quotient ((Train).wagonSetoid μ)) (x : Vertex)
    (ha : Parent (StdEdge i a) = W) (hb : Parent (StdEdge j b) = W)
    (hxa : x ∈ (StdEdge i a).1) (hxb : x ∈ (StdEdge j b).1) :
    ∃ r : OldACarrierEdge A R,
      Parent (CoreActual r) = W ∧ x ∈ (CoreActual r).1 := by
  obtain ⟨s, _t, _hsOld, _htOld, hsW, _htW, hxs, _hxt⟩ :=
    generatedActualASupportTrain_two_standard_vertex_shared_witnesses
      A hA C α R f T U hShared hRel μ hBound i j hij a b W x ha hb hxa hxb
  refine ⟨Emb i s, hsW, ?_⟩
  exact Eq.mpr (congrArg (fun Z : Set Vertex => x ∈ Z)
    (actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f (Emb i s))) hxs

end CoreVertexLocalization

end StructuralRamsey.Girth
