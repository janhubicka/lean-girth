import Girth.TrainCoreWagonBridge
import Girth.TrainSelectedCycleGeometricCutIncidence

/-!
# Geometric wagon cuts retain the actual output connector

The existing four-case cut theorem proves local witness incidence,
but discards the equality identifying the produced core wagon with
the physical output wagon W. This theorem proves that W belongs to
the image of the injective core-to-output wagon map at every real
owner cut, including mixed standard/core and core/core cuts.

For a standard/core cut, the physical core edge occurrence itself
identifies W. For a standard/standard cut, two standard incidence
edges have the same W; the cross-standard generator lemma supplies
a genuine shared old edge s, and TrainCoreWagonBridge identifies W
with the output class of s's embedded core wagon.

The theorem asserts this precisely for the *actual* attached
selected-picture BigCycle. It is not an A1--A3 transfer, nor does
it construct all target cut connectors or the full witness reduct.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SelectedCutCoreConnector

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "SharedEdge" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h)
  hShared μ

include hRel

/-- At any genuine cyclic change of geometric owner, a physical output
wagon connector has a UNIQUE ancestor core wagon, via the injected
core-wagon quotient classes. This retains its identity, rather than
merely asserting that some local shared edge has a core parent. -/
theorem attachedSelectedPicture_geometric_wagon_cut_in_core_range
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n)
    (W : Quotient ((Train).wagonSetoid μ))
    (hW : K.connector k = Sum.inr W)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    ∃ c : Quotient (U.wagonSetoid μ), CoreWagon c = W := by
  have hCoreLeft (b : CoreEdge)
      (hLabel : K.label k = Sum.inr (CoreActual b)) :
      CoreWagon (Quotient.mk (U.wagonSetoid μ) b) = W := by
    have hIncident : (Out).Meets (Sum.inr (CoreActual b)) W := by
      have h := K.left_incident k
      rw [hLabel, hW] at h
      exact h
    obtain ⟨edge, hEdge, hParent⟩ := hIncident
    have hEdgeEq : edge = CoreActual b := hEdge
    subst edge
    rw [generatedActualASupportTrain_coreWagonEmbedding_mk]
    exact hParent
  have hCoreRight (b : CoreEdge)
      (hLabel : K.label (cyclicSucc k) = Sum.inr (CoreActual b)) :
      CoreWagon (Quotient.mk (U.wagonSetoid μ) b) = W := by
    have hIncident : (Out).Meets (Sum.inr (CoreActual b)) W := by
      have h := K.right_incident k
      rw [hLabel, hW] at h
      exact h
    obtain ⟨edge, hEdge, hParent⟩ := hIncident
    have hEdgeEq : edge = CoreActual b := hEdge
    subst edge
    rw [generatedActualASupportTrain_coreWagonEmbedding_mk]
    exact hParent
  rcases cyclicOwnerCut_four_cases owner k hCut with
    ⟨i, j, hij, hi, hj⟩ | ⟨i, b, hi, hb⟩ |
    ⟨b, i, hb, hi⟩ | ⟨b, c, hbc, hb, hc⟩
  · obtain ⟨edgeA, edgeB, hEdgeA, hWA, hEdgeB, hWB⟩ :=
      OrderOneData.BigCycle.wagon_boundary_incidence_edges Out K k W hW
    have hContainedA : (Out).carrier (K.label k) ⊆
        copyCarrier (Std i) := by
      have h := hAllowed k
      rw [hi] at h
      exact h
    have hContainedB : (Out).carrier (K.label (cyclicSucc k)) ⊆
        copyCarrier (Std j) := by
      have h := hAllowed (cyclicSucc k)
      rw [hj] at h
      exact h
    obtain ⟨oldA, hParentA⟩ := attachedSelectedPicture_geometric_wagon_source
      A hA B D C family selected e R f T U hShared μ
      i (K.label k) W hContainedA ⟨edgeA, hEdgeA, hWA⟩
    obtain ⟨oldB, hParentB⟩ := attachedSelectedPicture_geometric_wagon_source
      A hA B D C family selected e R f T U hShared μ
      j (K.label (cyclicSucc k)) W hContainedB ⟨edgeB, hEdgeB, hWB⟩
    have hSame : Train.rel μ (StdEdge i oldA) (StdEdge j oldB) :=
      Quotient.exact (hParentA.trans hParentB.symm)
    obtain ⟨c, s, t, hsOld, htOld, hsCore, htCore, hsLocal, htLocal⟩ :=
      generatedActualASupportTrain_cross_standard_copy_local_incidence
        A hA C.toRelStructure S R f T U hShared hRel μ
        i j hij oldA oldB hSame
    refine ⟨Quotient.mk (U.wagonSetoid μ) (Emb i s), ?_⟩
    exact (generatedActualASupportTrain_standard_parent_eq_coreEmbedding
      A hA C.toRelStructure S R f T U hShared hRel
      μ i oldA s W hParentA hsOld).symm
  · have hCoreLabel :
        K.label (cyclicSucc k) = Sum.inr (CoreActual b) := by
      have h := hAllowed (cyclicSucc k)
      rw [hb] at h
      exact h
    exact ⟨Quotient.mk (U.wagonSetoid μ) b,
      hCoreRight b hCoreLabel⟩
  · have hCoreLabel : K.label k = Sum.inr (CoreActual b) := by
      have h := hAllowed k
      rw [hb] at h
      exact h
    exact ⟨Quotient.mk (U.wagonSetoid μ) b,
      hCoreLeft b hCoreLabel⟩
  · have hCoreLabel : K.label k = Sum.inr (CoreActual b) := by
      have h := hAllowed k
      rw [hb] at h
      exact h
    exact ⟨Quotient.mk (U.wagonSetoid μ) b,
      hCoreLeft b hCoreLabel⟩

end SelectedCutCoreConnector
end StructuralRamsey.Girth
