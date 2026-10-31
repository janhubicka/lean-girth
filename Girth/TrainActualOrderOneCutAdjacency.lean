import Girth.TrainActualOrderOneCutBridge

/-!
# An actual order-one reduct has adjacent source cuts

The physical bridge from the previous module meets BOTH retained source
connectors. One is a vertex and one a wagon. Thus the vertex belongs to
the actual output wagon carrier, and source A2 places its position
immediately before or after the wagon position. In a two-cut owner word
this is precisely the singleton-segment alternative.

No minimum-owner premise is needed for this step. The theorem retains
both canonical cut indices and both connector kinds, including wrap.
It does not yet construct the legal short replacement or apply the old
bound inside the receiving standard. No appendix.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A physical edge meeting a vertex connector and a wagon connector
forces those two positions to be adjacent by A2 alone. -/
theorem BigCycle.mixed_connectors_adjacent_of_common_edge
    {n : ℕ} (K : D.BigCycle n) (hA2 : K.A2)
    (a b : Fin n) (x : V) (p : P) (e : E)
    (hVertex : K.connector a = Sum.inl x)
    (hWagon : K.connector b = Sum.inr p)
    (hAtVertex : D.Incident (Sum.inr e) (K.connector a))
    (hAtWagon : D.Incident (Sum.inr e) (K.connector b)) :
    a = trainCyclicPred b ∨ a = cyclicSucc b := by
  have hx : x ∈ D.edgeCarrier e := by
    simpa only [hVertex, Incident, carrier] using hAtVertex
  have hMeet : D.Meets (Sum.inr e) p := by
    simpa only [hWagon, Incident] using hAtWagon
  obtain ⟨f, hf, hParent⟩ := hMeet
  have hfe : f = e := by
    simpa only [edges, Set.mem_singleton_iff] using hf
  subst f
  exact hA2.1 b p hWagon a ⟨x, hVertex, e, hParent, hx⟩

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualOrderOneCutAdjacency

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
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
    (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The genuine order-one cut reduct supplies its two actual connector
positions, of opposite kinds, which are adjacent in the ORIGINAL cycle.
Their equality with canonical cut indices is retained, not postulated. -/
theorem attachedSelectedPicture_orderOne_cut_positions_adjacent
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hAccept : K.Acceptable)
    (hBound : (Wit).Bound)
    (hOrder : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).twiceOrder = 2) :
    ∃ (a b : Fin (cyclicOwnerChanges owner))
      (x : Y) (p : Quotient (U.wagonSetoid μ)),
      a ≠ b ∧
      K.connector (cyclicOwnerCutIndex owner a) = Sum.inl (CoreEmb x) ∧
      K.connector (cyclicOwnerCutIndex owner b) = Sum.inr (CoreWagon p) ∧
      (cyclicOwnerCutIndex owner a =
        trainCyclicPred (cyclicOwnerCutIndex owner b) ∨
       cyclicOwnerCutIndex owner a =
        cyclicSucc (cyclicOwnerCutIndex owner b)) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨x, p, ⟨a, b, hab, hVertex, hWagon⟩, _⟩ :=
    attachedSelectedPicture_geometric_cut_orderOne_bridges
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hBound hOrder
  obtain ⟨edge, _, hInc⟩ :=
    attachedSelectedPicture_orderOne_cut_physical_bridge
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hBound hOrder a
  have hMap (j : Fin (cyclicOwnerChanges owner)) :
      Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  have hv : K.connector (cyclicOwnerCutIndex owner a) =
      Sum.inl (CoreEmb x) := by
    rw [← hMap a, hVertex]
    rfl
  have hw : K.connector (cyclicOwnerCutIndex owner b) =
      Sum.inr (CoreWagon p) := by
    rw [← hMap b, hWagon]
    rfl
  refine ⟨a, b, x, p, hab, hv, hw, ?_⟩
  exact OrderOneData.BigCycle.mixed_connectors_adjacent_of_common_edge
    (Out) K hAccept.2.1
    (cyclicOwnerCutIndex owner a) (cyclicOwnerCutIndex owner b)
    (CoreEmb x) (CoreWagon p) (CoreActual edge)
    hv hw (hInc a) (hInc b)

end ActualOrderOneCutAdjacency
end StructuralRamsey.Girth
