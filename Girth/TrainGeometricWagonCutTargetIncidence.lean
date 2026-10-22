import Girth.TrainSelectedWagonCutCoreMap
import Girth.TrainActualCutConnectorLift

/-!
# Actual wagon-cut incidences in the witness big-cycle reduct

At a geometric owner change with a physical output wagon connector,
the verified core-wagon injection determines the UNIQUE witness wagon.
For either core-edge owner, the output BigCycle incidence identifies
its literal core edge class. For either standard owner, pull the
corresponding physical output incidence edge back to its old standard
and obtain a genuinely shared old/core edge in the same wagon.

The standard/standard case uses the cross-standard shared-edge
incidence theorem, rather than silently choosing unrelated classes.
The mixed cases use exact old/core train reflection. Thus no target
incidence or output-wagon equality is postulated.

This does not construct the cut-indexed word, assert order-one A1
or prove the global cycle-reduction theorem.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section GeometricWagonCutIncidence

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
local notation "Wit" => sharedWitnessOrderOneData U μ Emb
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- Every true geometric wagon cut is incident to BOTH owner labels
in the genuine witness, using the unique core preimage of the
physical wagon connector. No global witness-reduct hypothesis. -/
theorem attachedSelectedPicture_geometric_wagon_cut_target_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (p : Quotient (U.wagonSetoid μ))
    (hW : K.connector k = Sum.inr (CoreWagon p))
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (Wit).Incident (owner k) (Sum.inr p) ∧
      (Wit).Incident (owner (cyclicSucc k)) (Sum.inr p) := by
  have hWagonInj : Function.Injective CoreWagon :=
    (generatedActualASupportTrain_coreWagonEmbedding
      A hA C.toRelStructure S R f T U
      (fun ν j s t hs => (hRel ν j s t).mp hs)
      hShared μ).injective
  have hStandard (i : I) (s : SharedEdge)
      (hs : Quotient.mk (U.wagonSetoid μ) (Emb i s) = p) :
      (Wit).Incident (Sum.inl i) (Sum.inr p) := by
    change (Wit).Meets (Sum.inl i) p
    exact ⟨Emb i s, ⟨s, rfl⟩, hs⟩
  have hCore (b : CoreEdge)
      (hb : Quotient.mk (U.wagonSetoid μ) b = p) :
      (Wit).Incident (Sum.inr b) (Sum.inr p) := by
    change (Wit).Meets (Sum.inr b) p
    exact ⟨b, rfl, hb⟩
  have hCoreLeft (b : CoreEdge)
      (hLabel : K.label k = Sum.inr (CoreActual b)) :
      Quotient.mk (U.wagonSetoid μ) b = p := by
    have hIncident := K.left_incident k
    rw [hLabel, hW] at hIncident
    change (Out).Meets (Sum.inr (CoreActual b)) (CoreWagon p) at hIncident
    obtain ⟨edge, he, hp⟩ := hIncident
    have heq : edge = CoreActual b := he
    subst edge
    have hClass : CoreWagon (Quotient.mk (U.wagonSetoid μ) b) =
        CoreWagon p := by
      rw [generatedActualASupportTrain_coreWagonEmbedding_mk]
      exact hp
    exact hWagonInj hClass
  have hCoreRight (b : CoreEdge)
      (hLabel : K.label (cyclicSucc k) = Sum.inr (CoreActual b)) :
      Quotient.mk (U.wagonSetoid μ) b = p := by
    have hIncident := K.right_incident k
    rw [hLabel, hW] at hIncident
    change (Out).Meets (Sum.inr (CoreActual b)) (CoreWagon p) at hIncident
    obtain ⟨edge, he, hp⟩ := hIncident
    have heq : edge = CoreActual b := he
    subst edge
    have hClass : CoreWagon (Quotient.mk (U.wagonSetoid μ) b) =
        CoreWagon p := by
      rw [generatedActualASupportTrain_coreWagonEmbedding_mk]
      exact hp
    exact hWagonInj hClass
  rcases cyclicOwnerCut_four_cases owner k hCut with
    ⟨i, j, hij, hi, hj⟩ | ⟨i, b, hi, hb⟩ |
    ⟨b, i, hb, hi⟩ | ⟨b, c, _hbc, hb, hc⟩
  · obtain ⟨edgeA, edgeB, hEdgeA, hWA, hEdgeB, hWB⟩ :=
      OrderOneData.BigCycle.wagon_boundary_incidence_edges
        Out K k (CoreWagon p) hW
    have hContainedA : (Out).carrier (K.label k) ⊆ copyCarrier (Std i) := by
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
      i (K.label k) (CoreWagon p) hContainedA ⟨edgeA, hEdgeA, hWA⟩
    obtain ⟨oldB, hParentB⟩ := attachedSelectedPicture_geometric_wagon_source
      A hA B D C family selected e R f T U hShared μ
      j (K.label (cyclicSucc k)) (CoreWagon p) hContainedB
      ⟨edgeB, hEdgeB, hWB⟩
    have hSame : (Train).rel μ (StdEdge i oldA) (StdEdge j oldB) :=
      Quotient.exact (hParentA.trans hParentB.symm)
    obtain ⟨c, s, t, hsOld, _htOld, hsCore, htCore, _hsLocal, _htLocal⟩ :=
      generatedActualASupportTrain_cross_standard_copy_local_incidence
        A hA C.toRelStructure S R f T U hShared hRel μ
        i j hij oldA oldB hSame
    have hCoreEq : CoreWagon (Quotient.mk (U.wagonSetoid μ) (Emb i s)) =
        CoreWagon p :=
      (generatedActualASupportTrain_standard_parent_eq_coreEmbedding
        A hA C.toRelStructure S R f T U hShared hRel
        μ i oldA s (CoreWagon p) hParentA hsOld).symm
    have hsP : Quotient.mk (U.wagonSetoid μ) (Emb i s) = p :=
      hWagonInj hCoreEq
    have htP : Quotient.mk (U.wagonSetoid μ) (Emb j t) = p :=
      (htCore.trans hsCore.symm).trans hsP
    constructor
    · rw [hi]
      exact hStandard i s hsP
    · rw [hj]
      exact hStandard j t htP
  · obtain ⟨_old, s, _hsOld, hsRel, _hsLocal⟩ :=
      attachedSelectedPicture_geometric_wagon_standard_core
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k (CoreWagon p) i b hW hi hb
    have hLabel : K.label (cyclicSucc k) = Sum.inr (CoreActual b) := by
      have h := hAllowed (cyclicSucc k)
      rw [hb] at h
      exact h
    have hbP := hCoreRight b hLabel
    have hsP : Quotient.mk (U.wagonSetoid μ) (Emb i s) = p :=
      (Quotient.sound hsRel).trans hbP
    constructor
    · rw [hi]
      exact hStandard i s hsP
    · rw [hb]
      exact hCore b hbP
  · obtain ⟨_old, s, _hsOld, hsRel, _hsLocal⟩ :=
      attachedSelectedPicture_geometric_wagon_core_standard
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k (CoreWagon p) i b hW hb hi
    have hLabel : K.label k = Sum.inr (CoreActual b) := by
      have h := hAllowed k
      rw [hb] at h
      exact h
    have hbP := hCoreLeft b hLabel
    have hsP : Quotient.mk (U.wagonSetoid μ) (Emb i s) = p :=
      (Quotient.sound hsRel).trans hbP
    constructor
    · rw [hb]
      exact hCore b hbP
    · rw [hi]
      exact hStandard i s hsP
  · have hLabelB : K.label k = Sum.inr (CoreActual b) := by
      have h := hAllowed k
      rw [hb] at h
      exact h
    have hLabelC : K.label (cyclicSucc k) = Sum.inr (CoreActual c) := by
      have h := hAllowed (cyclicSucc k)
      rw [hc] at h
      exact h
    have hbP := hCoreLeft b hLabelB
    have hcP := hCoreRight c hLabelC
    constructor
    · rw [hb]
      exact hCore b hbP
    · rw [hc]
      exact hCore c hcP

end GeometricWagonCutIncidence
end StructuralRamsey.Girth
