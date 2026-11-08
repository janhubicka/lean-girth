import Girth.TrainActualTwoCutSingletonShortStandardTransfer
import Girth.TrainActualCoreSingletonConsecutiveCuts
import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainEdgeLabelSupremeShort
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a two-cut standard/core-edge witness has a real source short transfer

For n>=3, exactly two geometric owner cuts, one reduced designated
standard i and the other reduced label a physical core edge b, the
real witness FullSystemGirthGT makes the cut-reduced word acceptable:
A2/A3 transfer from the original source and A1 holds because of i.
At cutoff q the globally legal reduced supreme target must be i,
since the other occurrence is a physical edge and the reduced length
is exactly two.

The merged physical-edge-label theorem forces the chosen supreme plan's
non-target piece to be ShortValid. The actual core owner is a singleton
source occurrence with precisely the two canonical boundary cuts.
The verified one-short/all-keep original source standard transfer then
yields complete K.HasSimultaneousSupreme, not merely a rank descent.

This disposes of the mixed standard/core-edge two-cut case of length
at least three without an abstract source designated B-label, a
synthetic witness owner, or any support pruning. No appendix or TeX.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutStandardCoreShort

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
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel


/-- With EXACTLY TWO geometric owner cuts, if one reduced label is
a genuine designated standard and the other is a physical core
A-edge, full witness system girth and the actual old supreme bound
give full ORIGINAL source simultaneous supremeness.

The edge-labelled source run is automatically singleton and the
reduced supreme target is forced to be the designated standard.
No independent physical source replacement is postulated. -/
theorem attachedSelectedPicture_two_cut_standard_core_full_supreme
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a c : OldEdge,
      a ≠ c ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        c.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (cut : Fin (cyclicOwnerChanges owner)) (i : I) (b : CoreEdge)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label (trainCyclicPred cut) = Sum.inl i)
    (hSource : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label cut = Sum.inr b)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hBounds :=
    attachedSelectedPicture_geometric_cut_restriction_bounds
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hAccept.2.1 hAccept.2.2
  have hAcceptZ : Z.Acceptable := by
    refine ⟨?_, hBounds.2.2.1, hBounds.2.2.2⟩
    intro _
    refine ⟨trainCyclicPred cut, ?_⟩
    change (Wit).designated (Z.label (trainCyclicPred cut))
    rw [hTarget]
    trivial
  have hOrderZ : Z.twiceOrder ≤ 2 * q :=
    hBounds.2.1.trans hOrder
  have hSupreme : Z.HasSimultaneousSupreme :=
    hWitness.2 _ Z hAcceptZ hOrderZ
  obtain ⟨k, hk, pieces, hPlan, hProduces⟩ := hSupreme
  have hkEq : k = trainCyclicPred cut := by
    have hkc : k ≠ cut := by
      intro heq
      subst k
      have hFalse : False := by
        simpa [OrderOneData.designated, hSource] using hk
      exact hFalse.elim
    have hPredNe : trainCyclicPred cut ≠ cut := by
      intro heq
      have hSucc := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
      rw [heq] at hSucc
      exact (cyclicSucc_ne_self_of_two_le hCuts cut) hSucc
    apply Fin.ext
    have hkBound := k.isLt
    have hCutBound := cut.isLt
    have hPredBound := (trainCyclicPred cut).isLt
    have hkVal : k.val ≠ cut.val := by
      intro h
      exact hkc (Fin.ext h)
    have hPredVal : (trainCyclicPred cut).val ≠ cut.val := by
      intro h
      exact hPredNe (Fin.ext h)
    omega
  subst k
  have hAt : Z.HasSupremeAt Wit (trainCyclicPred cut) :=
    ⟨hk, pieces, hPlan, hProduces⟩
  obtain ⟨_pieces, bridge, _hPlan, _hGlobal, _hSelected, hShort⟩ :=
    Z.hasSupremeAt_short_of_edge_label
      Wit (trainCyclicPred cut) cut i b hTarget hSource hAt
  let pos : Fin n := cyclicOwnerCutIndex owner cut
  have hCoreOwner : owner pos = Sum.inr b := by
    change owner (cyclicOwnerCutIndex owner cut) = Sum.inr b at hSource
    exact hSource
  obtain ⟨j, hHere, hPrev⟩ :=
    attachedSelectedPicture_core_singleton_consecutive_cut_indices
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed pos b hCoreOwner
  have hjEq : j = cut := by
    apply (cyclicOwnerCutIndex owner).injective
    simpa [pos] using hHere
  have hPrevious :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred pos := by
    rw [← hjEq]
    exact hPrev
  have hForward :
      cyclicOwnerCutIndex owner cut =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) := by
    change pos =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))
    rw [hPrevious]
    exact (cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) pos).symm
  exact attachedSelectedPicture_two_cut_singleton_short_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwo cut hForward i hTarget
    bridge hShort hOldSupreme

end ActualTwoCutStandardCoreShort
end StructuralRamsey.Girth
