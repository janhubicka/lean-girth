import Girth.TrainInteriorParentQuotientBridge
import Girth.TrainActualSupportParameterTransport

/-!
# Universal top requires no order-one cycle assumption

A two-occurrence mixed cycle asks a designated label for an edge
joining a given vertex to a given wagon. If the wagon parent map
is constant and the designated copy's vertices are covered by
its own edges, this bridge is automatic. In particular, the
shared-witness order-one bound at the universal train top holds
without any A1--A3 system-girth premise.

This is a structural fact about the exact order-one fragment, not a
full theorem about arbitrary acceptable big cycles.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E I P : Type v}

/-- A constant edge-to-parent map gives every designated label the
required bridge, provided its vertices are supported by its edges.
In particular all exact order-one cycles have a supreme label. -/
theorem OrderOneData.bound_of_constant_parent
    (D : OrderOneData V E I P)
    (hCover : ∀ i x, x ∈ D.copyCarrier i →
      ∃ e, e ∈ D.copyEdges i ∧ x ∈ D.edgeCarrier e)
    (hConst : ∀ e f : E, D.parent e = D.parent f) :
    D.Bound := by
  intro C
  have hBridge : ∀ (a : I ⊕ E) (x : V) (p : P),
      x ∈ D.carrier a → D.Meets a p →
      D.Bridge a x p := by
    intro a x p hx hm
    cases a with
    | inl i =>
        obtain ⟨e, he, hxe⟩ := hCover i x hx
        obtain ⟨b, _hb, hbp⟩ := hm
        exact ⟨e, he, (hConst e b).trans hbp, hxe⟩
    | inr e =>
        exact D.edge_bridge e x p hx hm
  rcases C.has_designated with hl | hr
  · exact Or.inl ⟨hl,
      hBridge C.left C.vertex C.wagon C.left_vertex C.left_meets⟩
  · exact Or.inr ⟨hr,
      hBridge C.right C.vertex C.wagon C.right_vertex C.right_meets⟩

/-- In the exact physical shared-witness order-one model, every
actual core edge belongs to the single top wagon. Hence its
order-one bound needs NO witness system-girth assumption. -/
theorem sharedWitnessOrderOne_top_bound
    {m : ℕ}
    (T : EdgeTrainLevels E m)
    (inCore : I → V ↪ E)
    (edgeCarrier : E → Set P) :
    (sharedWitnessOrderOneData T
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
      inCore edgeCarrier).Bound := by
  let D := sharedWitnessOrderOneData T
    (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
    inCore edgeCarrier
  apply D.bound_of_constant_parent
  · intro i x hx
    rcases hx with ⟨s, hxs⟩
    exact ⟨inCore i s, ⟨s, rfl⟩, hxs⟩
  · intro e f
    exact Quotient.sound (T.top e f)

open StructuralRamsey.RelStructure
universe u
variable {L : RelLanguage.{u}} {UA Old Core : Type v}


/-- For the ACTUAL attached A-support train, top-parent parameter
preservation needs no order-one cycle bound. Core/source sibling
parameters and shared relation reflection are still assumed;
the top witness bridge is automatic. -/
theorem activeAttached_actualASupport_parentBound_at_top
    {m : ℕ}
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (B : StructuralRamsey.Partite.System L P Old)
    (α : UA → P)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding
      (B.toRelStructure.induce (activeCarrier A B α)) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B.toRelStructure) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (hνTop : ν = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hShared : ∀ i : I,
      Nonempty (SharedOldACarrierEdge A B.toRelStructure
        (activeCarrier A B α)))
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      oldTrain.rel κ
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) s)
        (sharedOldACarrierInclusion A B.toRelStructure
          (activeCarrier A B α) t) ↔
      coreTrain.rel κ
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i s)
        (sharedOldACarrierCoreEmbedding A B.toRelStructure
          (activeCarrier A B α) D f i t))
    (allowed : Set (RelStructure.Attachment.Vertex
      (activeCarrier A B α) (W := Core) (I := I)))
    (hOld : ∀ i : I,
      TrainParentIntersectionBound
        (oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B.toRelStructure
            (activeCarrier A B α) D f i) μ)
        (oldTrain.wagonParent μ ν hμν) allowed)
    (hCore : TrainParentIntersectionBound
      (coreTrain.wagonClassCarrier
        (attachedCoreAEdgeCarrier A B.toRelStructure
          (activeCarrier A B α) D f) μ)
      (coreTrain.wagonParent μ ν hμν) allowed) :
    TrainParentIntersectionBound
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).wagonClassCarrier
          (fun e : ActualAttachedAEdge A B.toRelStructure
            (activeCarrier A B α) D f => e.1) μ)
      ((generatedActualASupportTrain A hA B.toRelStructure
        (activeCarrier A B α) D f oldTrain coreTrain hShared).wagonParent μ ν hμν) allowed := by
  subst ν
  exact activeAttached_actualASupport_parentBound_of_orderOne
    A hA B α D f oldTrain coreTrain μ
    (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) hμν
    hShared hRel allowed hOld hCore
    (sharedWitnessOrderOne_top_bound coreTrain
      (sharedOldACarrierCoreEmbedding A B.toRelStructure
        (activeCarrier A B α) D f)
      (attachedCoreAEdgeCarrier A B.toRelStructure
        (activeCarrier A B α) D f))

end StructuralRamsey.Girth
