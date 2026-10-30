import Girth.TrainActualPositiveCutSupremeOrBridges

/-!
# Track A: a supreme geometric cut owner really names a standard

The selected witness BigCycle labels are the *geometric owners* at
actual indexed cuts. A designated supreme witness label therefore
specifies an honest standard index; it is not itself an original
designated B-copy label. We retain the INDEXED supreme plan to keep
track of precisely which cut selected the standard. At witness order
one the separate physical-bridge alternative is retained verbatim.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutChosenStandard

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
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- The INDEX of a designated supreme witness label is an indexed
geometric cut whose owner is an actual standard. This is the correct
chosen standard for the next physical replacement stage. -/
theorem attachedSelectedPicture_cut_supreme_selects_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSimultaneousSupreme) :
    ∃ (i : I) (j : Fin (cyclicOwnerChanges owner)),
      owner (cyclicOwnerCutIndex owner j) = Sum.inl i ∧
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).HasSupremeAt (Wit) j := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨j, hDesignated, pieces, hValid, hGlobal⟩ := hSupreme
  have hLabel : Z.label j = owner (cyclicOwnerCutIndex owner j) := rfl
  cases ho : owner (cyclicOwnerCutIndex owner j) with
  | inl i =>
      exact ⟨i, j, ho, ⟨hDesignated, pieces, hValid, hGlobal⟩⟩
  | inr b =>
      have hNot : ¬ (Wit).designated (Z.label j) := by
        rw [hLabel, ho]
        simp [OrderOneData.designated]
      exact False.elim (hNot hDesignated)

end ActualPositiveCutChosenStandard
end StructuralRamsey.Girth
