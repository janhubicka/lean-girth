import Girth.TrainSelectedWagonCutCoreMap
import Girth.TrainCyclicCutIndices

/-!
# Lift each actual geometric owner-cut connector to the witness core

At an actual cut, the output connector is either a vertex or a wagon.
For a vertex the verified four-case physical cut theorem produces an
actual witness-core vertex with the same output image. For a wagon the
preceding theorem finds a core wagon whose *injective* class embedding
is the precise output wagon.

Thus an actual cut-indexed sequence of target connectors can be chosen,
and its map back to the source cycle is an equality, without assuming
a connector map. This completes the connector-equality INPUT of
cutIndexedWord. Target label incidence, A1 at order one and A2/A3
transport on all target wagons are separate obligations. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section ActualCutConnectorLift

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The physical output connector of a genuine owner cut is the image
of some *actual* core vertex or core wagon. The source connector is
not changed: this is a literal equality in the output connector type. -/
theorem attachedSelectedPicture_geometric_cut_connector_lift
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (k : Fin n)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    ∃ q : Y ⊕ Quotient (U.wagonSetoid μ),
      Sum.map CoreEmb CoreWagon q = K.connector k := by
  cases hConnector : K.connector k with
  | inl x =>
    have hCases :=
      attachedSelectedPicture_geometric_vertex_cut_incidence
        A hA B D C family selected e R f T U hShared μ
        K owner hAllowed k x hConnector hCut
    have hCore : ∃ y : Y, CoreEmb y = x := by
      rcases hCases with h | h | h | h
      · obtain ⟨i, j, hij, hi, hj, y, hy, hyI, hyJ⟩ := h
        exact ⟨y, hy⟩
      · obtain ⟨i, b, hi, hb, y, hy, hyI, hyB⟩ := h
        exact ⟨y, hy⟩
      · obtain ⟨b, i, hb, hi, y, hy, hyI, hyB⟩ := h
        exact ⟨y, hy⟩
      · obtain ⟨b, c, hbc, hb, hc, y, hy, hyB, hyC⟩ := h
        exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hCore
    refine ⟨Sum.inl y, ?_⟩
    simp [hConnector, hy]
  | inr W =>
    obtain ⟨c, hc⟩ :=
      attachedSelectedPicture_geometric_wagon_cut_in_core_range
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed k W hConnector hCut
    refine ⟨Sum.inr c, ?_⟩
    simp [hConnector, hc]

/-- The cut-indexed target connector word is obtained from the
actual geometrical source, rather than being postulated. -/
noncomputable def attachedSelectedPicture_cutConnector
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (j : Fin (cyclicOwnerChanges owner)) :
    Y ⊕ Quotient (U.wagonSetoid μ) :=
  Classical.choose
    (attachedSelectedPicture_geometric_cut_connector_lift
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (cyclicOwnerCutIndex owner j)
      (cyclicOwnerCutIndex_is_change owner j))

/-- At every indexed cut (including wraparound), the chosen target
connector maps to the exact original source connector. -/
theorem attachedSelectedPicture_cutConnector_eq
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (j : Fin (cyclicOwnerChanges owner)) :
    Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
    K.connector (cyclicOwnerCutIndex owner j) := by
  unfold attachedSelectedPicture_cutConnector
  exact Classical.choose_spec
    (attachedSelectedPicture_geometric_cut_connector_lift
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (cyclicOwnerCutIndex owner j)
      (cyclicOwnerCutIndex_is_change owner j))

end ActualCutConnectorLift
end StructuralRamsey.Girth
