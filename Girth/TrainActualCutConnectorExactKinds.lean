import Girth.TrainActualCutIndexedBigCycle
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact kinds and parents of actual reduced cut-indexed connectors

The verified geometric-cut constructor gives a TRUE witness BigCycle
whose cut connector is mapped by the actual injective core vertex
and core wagon quotient embeddings to the unchanged original cut
connector. This module packages the two inverse-type consequences.

If the original selected output cut connector is an actual core
vertex CoreEmb x, the CHOSEN lower witness connector is exactly
Sum.inl x, not merely some vertex with the same physical carrier.
If the original connector is a labelled output wagon W, the
CHOSEN lower witness connector is exactly Sum.inr p for a REAL
core wagon p whose injective output image is literally W.

No arbitrary wagon representative, source-label identification,
unproved A1, output SupremeCycleBound or original two-cycle
orientation is used. This is the exact bridge interface for
the original n=2 mixed vertex/wagon case and the residual
two-cut parent-preserving piece transfer. Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v

section CutConnectorExactKinds
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
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
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The genuine selected lower BigCycle's chosen connector at any
actual owner cut is the literal core vertex x whenever the actual
original cut connector is CoreEmb x. -/
theorem attachedSelectedPicture_cutConnector_exact_core_vertex
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner)) (x : Y)
    (hVertex :
      K.connector (cyclicOwnerCutIndex owner cut) =
        Sum.inl (CoreEmb x)) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).connector cut = Sum.inl x := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hMap : Sum.map CoreEmb CoreWagon (Z.connector cut) =
      K.connector (cyclicOwnerCutIndex owner cut) :=
    attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed cut
  cases hc : Z.connector cut with
  | inl y =>
      have hXY : CoreEmb y = CoreEmb x := by
        have h := hMap
        rw [hc, hVertex] at h
        exact Sum.inl.inj h
      have hyx : y = x := (CoreEmb).injective hXY
      simp [hc, hyx]
  | inr p =>
      have hFalse : Sum.inr (CoreWagon p) =
          (Sum.inl (CoreEmb x) :
            RelStructure.Attachment.Vertex S (W := Y) (I := I) ⊕
              Quotient ((Train).wagonSetoid μ)) := by
        simpa [hc, hVertex] using hMap
      cases hFalse

/-- The genuine selected lower BigCycle's chosen connector at any
actual owner cut is a REAL core wagon with literal output parent W,
not a newly chosen unlabelled or coincident wagon carrier. -/
theorem attachedSelectedPicture_cutConnector_exact_core_wagon
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner))
    (W : Quotient ((Train).wagonSetoid μ))
    (hWagon :
      K.connector (cyclicOwnerCutIndex owner cut) = Sum.inr W) :
    ∃ w : Quotient (U.wagonSetoid μ),
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).connector cut = Sum.inr w ∧
      CoreWagon w = W := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hMap : Sum.map CoreEmb CoreWagon (Z.connector cut) =
      K.connector (cyclicOwnerCutIndex owner cut) :=
    attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed cut
  cases hc : Z.connector cut with
  | inl y =>
      have hFalse : (Sum.inl (CoreEmb y) :
            RelStructure.Attachment.Vertex S (W := Y) (I := I) ⊕
              Quotient ((Train).wagonSetoid μ)) = Sum.inr W := by
        simpa [hc, hWagon] using hMap
      cases hFalse
  | inr p =>
      have hPW : CoreWagon p = W := by
        have h := hMap
        rw [hc, hWagon] at h
        exact Sum.inr.inj h
      exact ⟨p, hc, hPW⟩

end CutConnectorExactKinds
end StructuralRamsey.Girth
