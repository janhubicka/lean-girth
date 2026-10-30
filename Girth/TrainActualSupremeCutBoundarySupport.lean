import Girth.TrainActualPositiveCutSupremeOrBridges
import Girth.TrainSupremeBoundaryEdgeCoverage
import Girth.TrainCoreContactReflection

/-!
# Physical boundary support for the positive-cut alternative

A supreme plan on the cut-defined witness identifies ONE shared-copy index.
At every cyclic cut it yields a genuine shared edge of that copy. The
existing core physical edge and quotient embeddings then transport the
edge's vertex/wagon incidence to the ORIGINAL selected output connector.
The order-one two-bridge alternative is preserved unchanged.

This does not identify the witness copy with an original designated B-label,
construct the intervening replacement pieces or prove the final output cycle
supreme. No appendix input.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualSupremeCutSupport

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
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
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

/-- Every literal physical CORE edge incidence lifts from the witness to
the selected attachment, for both vertex and wagon connectors. -/
theorem attachedSelectedPicture_core_edge_incident_lift
    (b : CoreEdge) (q : Y ⊕ Quotient (U.wagonSetoid μ))
    (hInc : (Wit).Incident (Sum.inr b) q) :
    (Out).Incident (Sum.inr (CoreActual b))
      (Sum.map CoreEmb CoreWagon q) := by
  cases q with
  | inl y =>
      change y ∈ b.1 at hInc
      change CoreEmb y ∈ (CoreActual b).1
      rw [actualAPictureEdgeEquiv_core_carrier
        A hA C.toRelStructure S R f b]
      exact ⟨y, hInc, rfl⟩
  | inr p =>
      change (Wit).Meets (Sum.inr b) p at hInc
      obtain ⟨t, ht, hp⟩ := hInc
      have htb : t = b := ht
      subst t
      change (Out).Meets (Sum.inr (CoreActual b)) (CoreWagon p)
      refine ⟨CoreActual b, rfl, ?_⟩
      calc
        Quotient.mk ((generatedActualASupportTrain
          A hA C.toRelStructure S R f T U hShared).wagonSetoid μ)
          (CoreActual b) =
          CoreWagon (Quotient.mk (U.wagonSetoid μ) b) :=
            (generatedActualASupportTrain_coreWagonEmbedding_mk
              A hA C.toRelStructure S R f T U
              (fun ν j p q h => Iff.mp (hRel ν j p q) h)
              hShared μ b).symm
        _ = CoreWagon p := congrArg CoreWagon hp

/-- The genuine positive-cut dichotomy, now with a physical supporting
SHARED edge of one fixed witness copy at every original cut connector. -/
theorem attachedSelectedPicture_positive_cut_shared_boundary_support_or_bridges
    {n q : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hAccept : K.Acceptable)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    (∃ (k : Fin (cyclicOwnerChanges owner)) (i : I),
        Z.label k = Sum.inl i ∧
        ∀ j : Fin (cyclicOwnerChanges owner), ∃ s : Shared,
          (Wit).Incident (Sum.inr (Emb i s)) (Z.connector j) ∧
          (Out).Incident (Sum.inr (CoreActual (Emb i s)))
            (K.connector (cyclicOwnerCutIndex owner j))) ∨
      ∃ (x : Y) (p : Quotient (U.wagonSetoid μ)),
        (∃ i j : Fin (cyclicOwnerChanges owner), i ≠ j ∧
          Z.connector i = Sum.inl x ∧ Z.connector j = Sum.inr p) ∧
        ∀ k, (Wit).Bridge (Z.label k) x p := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hAlternative := attachedSelectedPicture_positive_cut_supreme_or_bridges
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts hAccept hq hWitness hOrder
  rcases hAlternative with hSup | hBridge
  · left
    obtain ⟨k, i, hk, hEdges⟩ :=
      sharedWitness_supreme_shared_edge_at_every_connector U μ Emb
        (Subtype.val : CoreEdge → Set Y) Z hSup
    refine ⟨k, i, hk, ?_⟩
    intro j
    obtain ⟨s, hs⟩ := hEdges j
    refine ⟨s, hs, ?_⟩
    have hLift := attachedSelectedPicture_core_edge_incident_lift
      A hA B D C family selected e R f T U hShared hRel μ
      (Emb i s) (Z.connector j) hs
    have hEq : Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) := by
      change Sum.map CoreEmb CoreWagon
        (attachedSelectedPicture_cutConnector
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
      exact attachedSelectedPicture_cutConnector_eq
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j
    simpa only [hEq] using hLift
  · exact Or.inr hBridge

end ActualSupremeCutSupport
end StructuralRamsey.Girth
