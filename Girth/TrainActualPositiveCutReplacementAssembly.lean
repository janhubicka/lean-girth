import Girth.TrainArbitraryReplacementComplete
import Girth.TrainActualZeroCutGlobalSupreme

/-!
# Assemble the standard-contained physical replacement

Once a geometric construction gives actual locally incident pieces whose
literal output is contained in one attached standard, the previously checked
global arbitrary-replacement lemma and actual zero-cut theorem finish the
positive-order transfer. The output wagon-linearity hypothesis is explicit
(Track B); the existence of such pieces is NOT asserted here (Track A).
This avoids identifying the reduced witness's supreme label with an
original designated B-label. No appendix input.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
section ActualPositiveCutReplacementAssembly

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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "OutWagon" => Quotient
  ((generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared).wagonSetoid μ)

include hRel

/-- The global positive-order pullback is automatic once physical local
replacement data and one-standard containment have been produced.
No extra designated target or global plan is postulated. -/
theorem attachedSelectedPicture_standard_contained_replacement_supreme
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (i : I)
    (pieces : Fin n → TrainSupremePiece ActualEdge OutWagon)
    (hInc : K.LocalPieceIncidence (Out) pieces)
    (hGeom : K.LocalLongA2Geometry (Out) pieces)
    (hFresh : ∀ (j : Fin n) (a : ActualEdge) (p : OutWagon)
        (b : ActualEdge), pieces j = .long a p b →
      ∀ t : Fin n, K.connector t ≠ Sum.inr p)
    (hContained : ∀ x ∈ K.resultWord (Out) pieces,
      (Out).carrier x.1 ⊆ copyCarrier (Std i)) :
    K.HasSimultaneousSupreme := by
  obtain ⟨r, Z, hWord, hZAccept, hZOrder, hPullback⟩ :=
    K.arbitrary_replacement_complete_of_three_le
      (Out) hAccept hLinear hn pieces hInc hGeom hFresh
  have hZContained : ∀ j : Fin r,
      (Out).carrier (Z.label j) ⊆ copyCarrier (Std i) := by
    intro j
    have hMem : (Z.label j, Z.connector j) ∈
        List.ofFn (fun t : Fin r => (Z.label t, Z.connector t)) := by
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    rw [hWord] at hMem
    exact hContained _ hMem
  obtain ⟨owner, hAllowed, hZero⟩ :=
    attachedSelectedPicture_geometric_zero_of_one_standard
      A hA B D C family selected e R f T U hShared μ Z i hZContained
  have hZBound : Z.twiceOrder ≤ 2 * q := by
    rw [hZOrder]
    exact hOrder
  have hZSup := attachedSelectedPicture_zero_cut_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwo hOldStrong hCoreStrong Z hZAccept
    hOldSupreme hZBound owner hAllowed hZero
  obtain ⟨kZ, hkZ, zPieces, hzValid, hzLegal⟩ := hZSup
  obtain ⟨kK, _hLabel, hKSup⟩ :=
    hPullback kZ ⟨hkZ, zPieces, hzValid, hzLegal⟩
  exact K.hasSimultaneousSupreme_of_hasSupremeAt (Out) kK hKSup

end ActualPositiveCutReplacementAssembly
end StructuralRamsey.Girth
