import Girth.TrainActualTwoCycleSourceExcludingDoubleWagon
import Girth.TrainTwoWagonCycleLocalObstruction
import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainCyclicCutIndexAtSourceTwo
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: original two-cut double-wagon cycle is forbidden by witness girth

At ORIGINAL source length two with both geometric cuts, the cut
enumerator is the identity. The actual cut-word is therefore a
Genuine two-occurrence lower-witness BigCycle, not an artificial
B-copy shadow. The exact physical connector embedding maps its
two witness connectors to the actual original core wagons.
They must both be wagons, so lower-witness FullSystemGirthGT q
and original order 4 (hence q>=2) contradict the generic
no-two-wagon local-piece obstruction. This supplies exactly
the outstanding hypothesis of the preceding n=2 source theorem.

The complete output-girth theorem below is a candidate until all
dependent originals and this new witness exclusion pass Lean/axioms.
No appendix, manuscript marker or support deletion.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCycleNoTwoWagons

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}
local notation "CutConnector" => attachedSelectedPicture_cutConnector
  A hA B D C family selected e R f T U hShared hRel μ

include hRel

/-- The original labelled source n=2 double-wagon case contradicts
true lower witness girth, without replacing its original B labels
by geometric owners. -/
theorem attachedSelectedPicture_two_cycle_no_double_wagon_of_witness
    {qcut : ℕ}
    (hWitness : (Wit).FullSystemGirthGT qcut)
    (K : (Out).BigCycle 2) (hOrder : K.twiceOrder ≤ 2 * qcut)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (w₀ w₁ : Quotient (U.wagonSetoid μ))
    (h0 : K.connector (0 : Fin 2) = Sum.inr (CoreWagon w₀))
    (h1 : K.connector (1 : Fin 2) = Sum.inr (CoreWagon w₁)) :
    False := by
  have hTwice : K.twiceOrder = 4 := by
    simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
      cyclicSucc, connectorKind, twiceOccurrenceWeight, h0, h1]
  have hq : 2 ≤ qcut := by omega
  have hLocal : (Wit).LocalPieceSystemBound 2 := by
    intro n Z' hAcceptZ hOrderZ
    exact (Wit).localPieceSystemBound_of_supremeCycleBound
      qcut hWitness.2 n Z' hAcceptZ
      (hOrderZ.trans (Nat.mul_le_mul_left 2 hq))
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  let j₀ : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let j₁ : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hIdx0 : cyclicOwnerCutIndex owner j₀ = (0 : Fin 2) := by
    apply Fin.ext
    simpa [j₀] using cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j₀
  have hIdx1 : cyclicOwnerCutIndex owner j₁ = (1 : Fin 2) := by
    apply Fin.ext
    simpa [j₁] using cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j₁
  have hImg0 :
      Sum.map CoreEmb CoreWagon (Z.connector j₀) =
        Sum.inr (CoreWagon w₀) := by
    have h := attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j₀
    change Sum.map CoreEmb CoreWagon (Z.connector j₀) =
      K.connector (cyclicOwnerCutIndex owner j₀) at h
    rw [hIdx0, h0] at h
    exact h
  have hImg1 :
      Sum.map CoreEmb CoreWagon (Z.connector j₁) =
        Sum.inr (CoreWagon w₁) := by
    have h := attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j₁
    change Sum.map CoreEmb CoreWagon (Z.connector j₁) =
      K.connector (cyclicOwnerCutIndex owner j₁) at h
    rw [hIdx1, h1] at h
    exact h
  obtain ⟨p, hp⟩ :
      ∃ p : Quotient (U.wagonSetoid μ), Z.connector j₀ = Sum.inr p := by
    cases hz : Z.connector j₀ with
    | inl x =>
        rw [hz] at hImg0
        cases hImg0
    | inr p =>
        exact ⟨p, hz⟩
  obtain ⟨q, hqW⟩ :
      ∃ q : Quotient (U.wagonSetoid μ), Z.connector j₁ = Sum.inr q := by
    cases hz : Z.connector j₁ with
    | inl x =>
        rw [hz] at hImg1
        cases hImg1
    | inr q =>
        exact ⟨q, hz⟩
  let Z₂ : (Wit).BigCycle 2 := hTwo ▸ Z
  have hp₂ : Z₂.connector (0 : Fin 2) = Sum.inr p := by
    cases hTwo
    simpa [Z₂, j₀] using hp
  have hq₂ : Z₂.connector (1 : Fin 2) = Sum.inr q := by
    cases hTwo
    simpa [Z₂, j₁] using hqW
  exact (Wit).BigCycle.two_wagon_impossible_of_localPieceSystemBound_two
    hLocal Z₂ p q hp₂ hq₂

/-- Candidate full one-level attached-output system girth.
This composes the real old selected bound, real witness bound,
literal original n=2 selected label and both n>=3 transfer branches.
The final double-wagon case is discharged by witness order-two girth.
Not a claim of the entire recursive partite forest theorem. -/
theorem attachedSelectedPicture_fullSystemGirth_of_actual_witness
    [Finite UA]
    (qcut : ℕ) (hqcut : 1 ≤ qcut)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound qcut)
    (hWitness : (Wit).FullSystemGirthGT qcut) :
    (Out).FullSystemGirthGT qcut := by
  apply attachedSelectedPicture_fullSystemGirth_of_no_double_wagon
    A hA B D C family selected e R f T U hShared hRel μ
    qcut hqcut hLinear hStrong hTwoCopies
    hOldStrong hCoreStrong hOldSupreme hWitness
  intro K hAccept hOrder owner hAllowed hTwo w₀ w₁ h0 h1
  exact attachedSelectedPicture_two_cycle_no_double_wagon_of_witness
    A hA B D C family selected e R f T U hShared hRel μ
    hWitness K hOrder owner hAllowed hTwo w₀ w₁ h0 h1

end ActualTwoCycleNoTwoWagons
end StructuralRamsey.Girth
