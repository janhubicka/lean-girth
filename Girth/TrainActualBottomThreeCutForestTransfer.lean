import Girth.TrainActualBottomForestReducedSupreme
import Girth.TrainActualPositiveCutStandardTransfer
import Girth.TrainActualReducedShortSingleton
import Girth.TrainCyclicRunIndexReverseWindow

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual bottom THREE-OR-MORE-CUT transfer from a mixed forest witness

A forest through the number of owner cuts gives a supreme plan in the
reduced witness. At the bottom each wagon is one edge, so the plan
only uses short replacements. Each short piece belongs to a singleton
source run, and its two physical contacts lift to the source cycle.
The resulting short replacements all lie in the chosen standard.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section BottomThreeCut

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S R f T U hShared
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (Fin.mk 0 (Nat.zero_lt_succ m))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

include hRel

/-- Transfer the short reduced plan to an original selected-copy supreme
plan for the source cycle with at least three geometric owner cuts. -/
theorem attachedSelectedPicture_bottom_three_cut_supreme_of_localForest
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOutputLinear : (Out).LinearPretrain)
    (H : (Wit).BottomForestGeometry)
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hBudget : cyclicOwnerChanges owner ≤ q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  have hReduced : Z.HasSimultaneousSupreme :=
    attachedSelectedPicture_bottom_reduced_supreme_of_localForest
      A hA B D C family selected e R f T U hShared hRel
      H q hLocal K owner hAllowed hCuts hBudget
      hAccept.2.1 hAccept.2.2
  classical
  obtain ⟨target, hDesignated, pieces, hPlan, _⟩ := hReduced
  obtain ⟨i, hTarget⟩ : ∃ i : I, Z.label target = Sum.inl i := by
    cases h : Z.label target with
    | inl i => exact ⟨i, rfl⟩
    | inr b =>
        rw [h] at hDesignated
        exact False.elim hDesignated
  let run := cyclicOwnerRunIndex owner (by omega : 0 < cyclicOwnerChanges owner)
  have hOwner (k : Fin n) : owner k = Z.label (run k) :=
    cyclicOwnerRunIndex_owner_eq_cut owner (by omega) k
  have hShortAt (k : Fin n) (hk : owner k ≠ Sum.inl i) :
      ∃ a : ActualEdge,
        (Out).Incident (.inr a) (K.connector (trainCyclicPred k)) ∧
        (Out).Incident (.inr a) (K.connector k) ∧
        a.1 ⊆ copyCarrier (Std i) := by
    have hDifferent : Z.label (run k) ≠ Z.label target := by
      rwa [← hOwner k, hTarget]
    have hPiece := (hPlan (run k)).2 hDifferent
    cases hKind : pieces (run k) with
    | keep =>
        rw [hKind] at hPiece
        exact False.elim hPiece
    | long a p b =>
        have hLong : Z.LongValid Wit target (run k) a p b := by
          simpa only [hKind] using hPiece
        obtain ⟨_, _, _, _, _, _, hNe, ha, hb, _⟩ := hLong
        exact (hNe (H.parent_injective (ha.trans hb.symm))).elim
    | short b =>
        have hShort : Z.ShortValid Wit target (run k) b := by
          simpa only [hKind] using hPiece
        have hForward :=
          attachedSelectedPicture_reduced_short_forces_singleton_three_cuts
            A hA B D C family selected e R f T U hShared hRel μBottom
            K hAccept owner hAllowed hThree target (run k) b hShort
        let pos := cyclicOwnerCutIndex owner (run k)
        have hPrev : cyclicOwnerCutIndex owner (trainCyclicPred (run k)) =
            trainCyclicPred pos := by
          change _ = trainCyclicPred (cyclicOwnerCutIndex owner (run k))
          rw [hForward, trainCyclicPred_cyclicSucc_of_two_le K.length_ge_two]
        have hkPos : k = pos := cyclicOwnerRunIndex_singleton_fibre
          owner K.length_ge_two hCuts (run k) pos k hPrev rfl rfl
        obtain ⟨hIncLeft, hIncRight⟩ :=
          attachedSelectedPicture_cut_short_piece_incident_lift
            A hA B D C family selected e R f T U hShared hRel μBottom
            K owner hAllowed hCuts target (run k) b hShort k
            hkPos.symm (hPrev.trans (congrArg trainCyclicPred hkPos.symm))
        exact ⟨CoreActual b, hIncLeft, hIncRight,
          attachedSelectedPicture_cut_short_piece_carrier_in_standard
            A hA B D C family selected e R f T U hShared hRel μBottom
            K owner hAllowed hCuts target (run k) i hTarget b hShort⟩
  let edge (k : Fin n) (hk : owner k ≠ Sum.inl i) := Classical.choose (hShortAt k hk)
  let expanded (k : Fin n) : TrainSupremePiece ActualEdge
      (Quotient ((Train).wagonSetoid μBottom)) :=
    if hk : owner k = Sum.inl i then .keep else .short (edge k hk)
  have hNoLong (k : Fin n) (a : ActualEdge)
      (p : Quotient ((Train).wagonSetoid μBottom)) (b : ActualEdge) :
      expanded k ≠ .long a p b := by
    by_cases hk : owner k = Sum.inl i <;> simp [expanded, hk]
  have hInc : K.LocalPieceIncidence Out expanded := by
    intro k
    by_cases hk : owner k = Sum.inl i
    · simp only [expanded, dif_pos hk]
    · have h := Classical.choose_spec (hShortAt k hk)
      simpa only [expanded, dif_neg hk] using And.intro h.1 h.2.1
  have hKeep (k : Fin n) (h : expanded k = .keep) : owner k = Sum.inl i := by
    by_contra hk
    simp [expanded, hk] at h
  have hShort (k : Fin n) (a : ActualEdge) (h : expanded k = .short a) :
      a.1 ⊆ copyCarrier (Std i) := by
    by_cases hk : owner k = Sum.inl i
    · simp [expanded, hk] at h
    · have heq : edge k hk = a := by simpa [expanded, hk] using h
      rw [← heq]
      exact (Classical.choose_spec (hShortAt k hk)).2.2
  exact attachedSelectedPicture_supreme_of_standard_replacement_of_three_le
    A hA B D C family selected e R f T U hShared hRel μBottom
    hStrong hTwo hOldStrong hCoreStrong K hAccept hOutputLinear hn hOrder
    owner hAllowed i expanded hInc
    (fun k a b p h => (hNoLong k a p b h).elim)
    (fun k a p b h => (hNoLong k a p b h).elim)
    hKeep hShort (fun k a p b h => (hNoLong k a p b h).elim) hOldSupreme


end BottomThreeCut
end StructuralRamsey.Girth
