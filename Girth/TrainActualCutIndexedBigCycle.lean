import Girth.TrainGeometricVertexCutTargetIncidence
import Girth.TrainGeometricWagonCutTargetIncidence
import Girth.TrainActualCoreRestrictionMap
import Girth.TrainCutIndexedWord

/-!
# The legal cut-indexed witness BigCycle for the actual picture step

This module combines the two *physical* target-incidence theorems. Every
genuine geometric change of owner has an exact core vertex/wagon
preimage, and BOTH source owner labels are incident with that exact
witness connector. The cyclic run/wrap identity identifies the owner
immediately after one cut with the owner at the next cut.

The already-verified generic cut-indexed-word constructor then builds a
legal witness BigCycle. The genuine core embedding supplies the
restriction map, so length, twice-order, A2 and A3 transfer. The proof
does not infer order-one A1 from coincident carriers: that designated
occurrence/bridge obligation remains separate. No cycle-transfer or
system-girth induction is asserted here.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualCutIndexedWitnessCycle

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
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "CutConnector" => attachedSelectedPicture_cutConnector
  A hA B D C family selected e R f T U hShared hRel μ

include hRel

/-- Both actual target incidences at every indexed geometric owner
cut, including wrap. The right target label is the owner at the
NEXT cut, not simply the next source occurrence. -/
theorem attachedSelectedPicture_cut_target_incidence
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (j : Fin (cyclicOwnerChanges owner)) :
    (Wit).Incident (owner (cyclicOwnerCutIndex owner j))
      (CutConnector K owner hAllowed j) ∧
    (Wit).Incident (owner (cyclicOwnerCutIndex owner (cyclicSucc j)))
      (CutConnector K owner hAllowed j) := by
  let k : Fin n := cyclicOwnerCutIndex owner j
  let q : Y ⊕ Quotient (U.wagonSetoid μ) :=
    CutConnector K owner hAllowed j
  have hConnector :
      Sum.map CoreEmb CoreWagon q = K.connector k :=
    attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  have hCut : owner k ≠ owner (cyclicSucc k) :=
    cyclicOwnerCutIndex_is_change owner j
  have hPair : (Wit).Incident (owner k) q ∧
      (Wit).Incident (owner (cyclicSucc k)) q := by
    cases hq : q with
    | inl y =>
        have hV : K.connector k = Sum.inl (CoreEmb y) := by
          simpa [hq] using hConnector.symm
        exact attachedSelectedPicture_geometric_vertex_cut_target_incidence
          A hA B D C family selected e R f T U hShared μ
          K owner hAllowed k y hV hCut
    | inr p =>
        have hW : K.connector k = Sum.inr (CoreWagon p) := by
          simpa [hq] using hConnector.symm
        exact attachedSelectedPicture_geometric_wagon_cut_target_incidence
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed k p hW hCut
  have hNext :
      owner (cyclicSucc (cyclicOwnerCutIndex owner j)) =
        owner (cyclicOwnerCutIndex owner (cyclicSucc j)) := by
    have h := cyclicOwnerRunLabel_eq_next_cut owner j
    change owner (cyclicSucc (cyclicOwnerCutIndex owner j)) =
      owner (cyclicOwnerCutIndex owner (cyclicSucc j)) at h
    exact h
  constructor
  · exact hPair.1
  · rw [← hNext]
    exact hPair.2

/-- The actual geometric cut word is a LEGAL typed witness BigCycle:
neither connector injectivity nor target incidences are assumptions.
Only the existence of a geometrically admissible owner choice and
at least two real cuts are required. -/
noncomputable def attachedSelectedPicture_geometric_cutBigCycle
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner) :
    (Wit).BigCycle (cyclicOwnerChanges owner) :=
  OrderOneData.cutIndexedWord K owner hCuts
    (fun x : I ⊕ CoreEdge => x)
    (fun _ _ h => h)
    (fun y => CoreEmb y)
    (fun p => CoreWagon p)
    (fun j => CutConnector K owner hAllowed j)
    (fun j => (attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j).symm)
    (fun j => (attachedSelectedPicture_cut_target_incidence
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j).1)
    (fun j => (attachedSelectedPicture_cut_target_incidence
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j).2)

/-- The verified physical core inclusion and physical cut-connector
equality instantiate the actual RestrictionMap with no additional
contact or pair-reflection premises. -/
noncomputable def attachedSelectedPicture_geometric_cut_restrictionMap
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner) :
    K.RestrictionMap
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts) :=
  attachedSelectedPicture_core_restrictionMap
    A hA B D C family selected e R f T U hShared
    (fun ν j p q hp => (hRel ν j p q).mp hp)
    μ K
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts)
    (cyclicOwnerCutIndex owner)
    (fun j => (attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j).symm)

/-- The actual physical cut-defined witness cycle does not increase
length or twice-order, and preserves A2 and A3 from the source.
Order-one A1 and the bridge alternative are NOT asserted. -/
theorem attachedSelectedPicture_geometric_cut_restriction_bounds
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hA2 : K.A2) (hA3 : K.A3) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    cyclicOwnerChanges owner ≤ n ∧ Z.twiceOrder ≤ K.twiceOrder ∧
      Z.A2 ∧ Z.A3 :=
  (attachedSelectedPicture_geometric_cut_restrictionMap
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts).restrict hA2 hA3

end ActualCutIndexedWitnessCycle
end StructuralRamsey.Girth
