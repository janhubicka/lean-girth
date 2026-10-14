import Girth.TrainTaggedQuotientCarrier
import Girth.TrainPhysicalWagonQuotientModel
import Girth.TrainInteriorParentQuotientBridge
import Girth.TrainTwoSourceBridge

/-!
# Parameter preservation on genuine generated physical wagon quotients

Compose the exact shared/private quotient normal form with the
two-source bridge criterion. The first theorem requires the bridge as
a premise; the second obtains it from the *exact order-one* condition
at the parent cut. Source old/core sibling bounds and physical owner
geometry remain explicit hypotheses.

This is not a derivation of order-one from the manuscript's full
A1--A3 system-girth invariant and is not the recursive Ramsey theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I Shared OldEdge CoreEdge : Type v}

/-- A two-source bridge, old/core sibling bounds, and the actual
shared-edge normal form imply the sibling parameter on *physical*
generated wagons, not just on abstract source labels. -/
theorem physicalGenerated_parentIntersectionBound_of_twoSource
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (oldEdges : I → OldEdge → Set W)
    (coreEdges : CoreEdge → Set W)
    (physicalEdges : PhysicalPictureEdge inOld I CoreEdge → Set W)
    (hCorePhysical : ∀ b,
      physicalEdges (physicalCoreEdge inOld I b) = coreEdges b)
    (hStdPhysical : ∀ i a,
      physicalEdges (physicalStandardEdge inOld inCore i a) =
        oldEdges i a)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound
        (Told.wagonClassCarrier (oldEdges i) μ)
        (Told.wagonParent μ ν hμν) allowed)
    (hCore : TrainParentIntersectionBound
      (Tcore.wagonClassCarrier coreEdges μ)
      (Tcore.wagonParent μ ν hμν) allowed)
    (hCoreInside : ∀ c : Quotient (Tcore.wagonSetoid μ),
      Tcore.wagonClassCarrier coreEdges μ c ⊆ coreVertices)
    (hOffCoreIndex : ∀ i j
        (u v : Quotient (Told.wagonSetoid μ)) (x : W),
      x ∉ coreVertices →
      x ∈ Told.wagonClassCarrier (oldEdges i) μ u →
      x ∈ Told.wagonClassCarrier (oldEdges j) μ v → i = j)
    (hTwoSource : ParentCoreTwoSourceBridge
      (fun i => Told.wagonClassCarrier (oldEdges i) μ)
      (Told.wagonParent μ ν hμν)
      (Tcore.wagonClassCarrier coreEdges μ)
      (Tcore.wagonParent μ ν hμν)
      (PhysicalWagonModel.contact Told Tcore inOld inCore μ)
      (PhysicalWagonModel.contact Told Tcore inOld inCore ν)
      coreVertices allowed) :
    TrainParentIntersectionBound
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonClassCarrier physicalEdges μ)
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonParent μ ν hμν) allowed := by
  have hContactParent : ∀ i u c,
      PhysicalWagonModel.contact Told Tcore inOld inCore μ i u = some c →
      PhysicalWagonModel.contact Told Tcore inOld inCore ν i
        (Told.wagonParent μ ν hμν u) =
          some (Tcore.wagonParent μ ν hμν c) := by
    intro i u c hc
    exact sharedWagonQuotient_contact_parent
      Told Tcore μ ν hμν (fun _ : I => inOld) inCore
      hRel i u c hc
  have hParentInjective : ∀ i
      (a b : Quotient (Told.wagonSetoid ν))
      (p : Quotient (Tcore.wagonSetoid ν)),
      PhysicalWagonModel.contact Told Tcore inOld inCore ν i a = some p →
      PhysicalWagonModel.contact Told Tcore inOld inCore ν i b = some p →
      a = b := by
    intro i a b p ha hb
    apply sharedWagonQuotient_glue_injective
      Told Tcore ν (fun _ : I => inOld) inCore (hRel ν) i
    calc
      gluedStandardNode
          (PhysicalWagonModel.contact Told Tcore inOld inCore ν) i a =
          Sum.inl p := by simp [gluedStandardNode, ha]
      _ = gluedStandardNode
          (PhysicalWagonModel.contact Told Tcore inOld inCore ν) i b := by
            simp [gluedStandardNode, hb]
  have hTagged : TrainParentIntersectionBound
      (GeneratedTaggedWagonCarrier
        (fun i => Told.wagonClassCarrier (oldEdges i) μ)
        (Tcore.wagonClassCarrier coreEdges μ)
        (PhysicalWagonModel.contact Told Tcore inOld inCore μ))
      (PhysicalWagonModel.parentTag Told Tcore inOld inCore μ ν hμν)
      allowed := by
    exact generatedTaggedWagon_parentIntersectionBound_of_twoSource
      (fun i => Told.wagonClassCarrier (oldEdges i) μ)
      (Told.wagonParent μ ν hμν)
      (Tcore.wagonClassCarrier coreEdges μ)
      (Tcore.wagonParent μ ν hμν)
      (PhysicalWagonModel.contact Told Tcore inOld inCore μ)
      (PhysicalWagonModel.contact Told Tcore inOld inCore ν)
      coreVertices allowed hOld hCore hCoreInside hOffCoreIndex
      hParentInjective hTwoSource hContactParent
  have hSource : TrainParentIntersectionBound
      (PhysicalWagonModel.sourceCarrier
        Told Tcore inOld inCore oldEdges coreEdges μ)
      (PhysicalWagonModel.parentTag Told Tcore inOld inCore μ ν hμν)
      allowed := by
    change TrainParentIntersectionBound
      (GeneratedTaggedWagonCarrier
        (taggedOldFiberCarrier
          (Quotient.mk (Told.wagonSetoid μ)) oldEdges)
        (taggedCoreFiberCarrier
          (Quotient.mk (Tcore.wagonSetoid μ)) coreEdges)
        (PhysicalWagonModel.contact Told Tcore inOld inCore μ))
      (PhysicalWagonModel.parentTag Told Tcore inOld inCore μ ν hμν)
      allowed
    rw [taggedOldFiberCarrier_eq_wagonClassCarrier Told oldEdges μ,
        taggedCoreFiberCarrier_eq_wagonClassCarrier Tcore coreEdges μ]
    exact hTagged
  exact PhysicalWagonModel.parentIntersectionBound
    Told Tcore inOld inCore hShared hRel
    oldEdges coreEdges physicalEdges hCorePhysical hStdPhysical
    μ ν hμν allowed hSource

/-- Specialise the physical generated-parameter theorem to the
two-source bridge obtained from the actual order-one witness cycle.
The order-one bound is required at the PARENT cut ν. -/
theorem physicalGenerated_parentIntersectionBound_of_orderOne
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hShared : ∀ i : I, Nonempty Shared)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (oldEdges : I → OldEdge → Set W)
    (coreEdges : CoreEdge → Set W)
    (physicalEdges : PhysicalPictureEdge inOld I CoreEdge → Set W)
    (hCorePhysical : ∀ b,
      physicalEdges (physicalCoreEdge inOld I b) = coreEdges b)
    (hStdPhysical : ∀ i a,
      physicalEdges (physicalStandardEdge inOld inCore i a) =
        oldEdges i a)
    (coreVertices allowed : Set W)
    (hOld : ∀ i : I,
      TrainParentIntersectionBound
        (Told.wagonClassCarrier (oldEdges i) μ)
        (Told.wagonParent μ ν hμν) allowed)
    (hCore : TrainParentIntersectionBound
      (Tcore.wagonClassCarrier coreEdges μ)
      (Tcore.wagonParent μ ν hμν) allowed)
    (hCoreInside : ∀ c : Quotient (Tcore.wagonSetoid μ),
      Tcore.wagonClassCarrier coreEdges μ c ⊆ coreVertices)
    (hOffCoreIndex : ∀ i j
        (u v : Quotient (Told.wagonSetoid μ)) (x : W),
      x ∉ coreVertices →
      x ∈ Told.wagonClassCarrier (oldEdges i) μ u →
      x ∈ Told.wagonClassCarrier (oldEdges j) μ v → i = j)
    (hSharedPhysical : ∀ i s,
      oldEdges i (inOld s) = coreEdges (inCore i s))
    (hPointCoveredEdge : ∀ i (e : OldEdge) (x : W),
      x ∈ coreVertices → x ∈ oldEdges i e →
      ∃ s : Shared, x ∈ oldEdges i (inOld s))
    (hOrderOne :
      (sharedWitnessOrderOneData Tcore ν inCore coreEdges).Bound) :
    TrainParentIntersectionBound
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonClassCarrier physicalEdges μ)
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonParent μ ν hμν) allowed := by
  have hBridge : ParentCoreTwoSourceBridge
      (fun i => Told.wagonClassCarrier (oldEdges i) μ)
      (Told.wagonParent μ ν hμν)
      (Tcore.wagonClassCarrier coreEdges μ)
      (Tcore.wagonParent μ ν hμν)
      (PhysicalWagonModel.contact Told Tcore inOld inCore μ)
      (PhysicalWagonModel.contact Told Tcore inOld inCore ν)
      coreVertices allowed := by
    exact interiorParent_twoSourceBridge_of_orderOne
      Told Tcore μ ν hμν (fun _ : I => inOld) inCore
      hRel oldEdges coreEdges hSharedPhysical
      coreVertices allowed hPointCoveredEdge hOrderOne
  exact physicalGenerated_parentIntersectionBound_of_twoSource
    Told Tcore μ ν hμν inOld inCore hShared hRel
    oldEdges coreEdges physicalEdges hCorePhysical hStdPhysical
    coreVertices allowed hOld hCore hCoreInside hOffCoreIndex hBridge

end StructuralRamsey.Girth
