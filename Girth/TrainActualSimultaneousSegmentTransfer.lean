import Girth.TrainActualThreeCutFromFullSystem
import Girth.TrainActualPositiveCutReplacementAssembly

/-!
# One simultaneous replacement of all non-target owner segments

An explicit certificate for the shortened circulation proof. The reduced
supreme plan is fixed once, and its physical source expansion is reused in
every obligation. The kept-occurrence equivalence records preservation of
all occurrences of the chosen geometric owner, including separated runs.

The actual global transfer below consumes this certificate through the
standard-contained arbitrary replacement theorem. No minimality hypothesis,
rank descent, successor-tree input, or appendix theorem is used.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualSimultaneousSegmentTransfer

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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

/-- The expanded plan preserves every occurrence owned by the selected
standard, and only those occurrences. In particular repeated occurrences
of the target owner in different maximal runs are all retained. -/
theorem attachedSelectedPicture_expanded_plan_keep_iff_target_owner
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (reduced : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).PlanValid Wit target reduced)
    (pos : Fin n) :
    cyclicExpandReducedPieces owner (by omega) reduced
      CoreActual CoreWagon pos = .keep ↔ owner pos = Sum.inl i := by
  constructor
  · exact attachedSelectedPicture_expanded_plan_keep_owned_by_target
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target i hTarget reduced hPlan pos
  · intro hOwner
    apply (cyclicExpandReducedPieces_keep_iff
      owner (by omega) reduced CoreActual CoreWagon pos).mpr
    apply (hPlan (cyclicOwnerRunIndex owner (by omega) pos)).1
    calc
      (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts).label
          (cyclicOwnerRunIndex owner (by omega) pos) =
          owner (cyclicOwnerCutIndex owner
            (cyclicOwnerRunIndex owner (by omega) pos)) :=
        attachedSelectedPicture_reduced_label_eq_source_owner
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed hCuts _
      _ = owner pos :=
        (cyclicOwnerRunIndex_owner_eq_cut owner (by omega) pos).symm
      _ = Sum.inl i := hOwner
      _ = _ := hTarget.symm

/-- A single globally legal reduced plan gives all physical obligations
for one simultaneous replacement of the original source cycle. The
conclusion exposes the exact source-indexed pieces, preserves all target
runs, proves inserted wagons fresh in the entire source, and places the
whole literal result word in the chosen standard.

No minimality of the owner assignment, occurrence descent, old girth
bound, or original designated target label is assumed. -/
theorem attachedSelectedPicture_fixed_plan_simultaneous_segment_certificate
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hOldStrong : AStrong A C.toRelStructure S)
    (target : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target = Sum.inl i)
    (reduced : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target reduced)
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit reduced) :
    let expanded := cyclicExpandReducedPieces owner (by omega)
      reduced CoreActual CoreWagon
    (∀ pos : Fin n, expanded pos = .keep ↔ owner pos = Sum.inl i) ∧
    K.LocalPieceIncidence Out expanded ∧
    K.LocalLongA2Geometry Out expanded ∧
    (∀ (pos : Fin n) (first : ActualEdge)
      (wagon : Quotient ((Train).wagonSetoid μ)) (second : ActualEdge),
      expanded pos = .long first wagon second →
        ∀ t : Fin n, K.connector t ≠ Sum.inr wagon) ∧
    (∀ entry ∈ K.resultWord Out expanded,
      (Out).carrier entry.1 ⊆ copyCarrier (Std i)) := by
  let expanded := cyclicExpandReducedPieces owner (by omega)
    reduced CoreActual CoreWagon
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hKeep : ∀ pos : Fin n,
      expanded pos = .keep ↔ owner pos = Sum.inl i :=
    attachedSelectedPicture_expanded_plan_keep_iff_target_owner
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target i hTarget reduced hPlan
  have hInc : K.LocalPieceIncidence Out expanded :=
    attachedSelectedPicture_expanded_plan_localPieceIncidence
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hOldStrong
      target reduced hPlan hProduces
  have hGeom : K.LocalLongA2Geometry Out expanded :=
    attachedSelectedPicture_expanded_plan_localLongA2Geometry
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hOldStrong target reduced hPlan
  have hFresh : ∀ (pos : Fin n) (first : ActualEdge)
      (wagon : Quotient ((Train).wagonSetoid μ)) (second : ActualEdge),
      expanded pos = .long first wagon second →
        ∀ t : Fin n, K.connector t ≠ Sum.inr wagon :=
    attachedSelectedPicture_expanded_plan_long_fresh
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hOldStrong
      target reduced hPlan hProduces
  obtain ⟨hShort, hLong⟩ :=
    attachedSelectedPicture_expanded_plan_edges_in_target_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target i hTarget reduced hPlan
  refine ⟨hKeep, hInc, hGeom, hFresh, ?_⟩
  apply K.resultWord_labels_of_piece_property Out expanded
    (fun label => (Out).carrier label ⊆ copyCarrier (Std i))
  intro pos
  cases hp : expanded pos with
  | keep =>
      have hOwner : owner pos = Sum.inl i := (hKeep pos).mp hp
      have h := hAllowed pos
      rw [hOwner] at h
      exact h
  | short first =>
      change first.1 ⊆ copyCarrier (Std i)
      exact hShort pos first hp
  | long first wagon second =>
      change first.1 ⊆ copyCarrier (Std i) ∧
        second.1 ⊆ copyCarrier (Std i)
      exact hLong pos first wagon second hp

/-- Direct three-or-more-cut transfer, assembled from the explicit
simultaneous segment certificate. The witness bound chooses one complete
reduced plan; all original target-owned runs are retained; the arbitrary
replacement theorem is applied once; the old standard bound gives the
supreme occurrence to pull back. The length assumption follows from the
injective enumeration of cuts, so only the actual cut-count hypothesis
is required here. -/
theorem attachedSelectedPicture_three_cut_simultaneous_segment_transfer
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCountBound : cyclicOwnerChanges owner ≤ n := by
    have hCard := Fintype.card_le_of_injective
      (cyclicOwnerCutIndex owner) (cyclicOwnerCutIndex owner).injective
    simpa using hCard
  have hn : 3 ≤ n := by omega
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hReduced : Z.HasSimultaneousSupreme :=
    attachedSelectedPicture_three_cut_reduced_supreme_of_fullSystem
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree hq hWitness hOrder
  obtain ⟨i, target, hOwner, hAt⟩ :=
    attachedSelectedPicture_cut_supreme_selects_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hReduced
  have hTarget : Z.label target = Sum.inl i := by
    change owner (cyclicOwnerCutIndex owner target) = Sum.inl i
    exact hOwner
  obtain ⟨_hChosen, reduced, hPlan, r, reducedOutput, hWord⟩ := hAt
  have hProduces : Z.PlanProducesBigCycle Wit reduced :=
    ⟨r, reducedOutput, hWord⟩
  obtain ⟨_hKeepAll, hInc, hGeom, hFresh, hContained⟩ :=
    attachedSelectedPicture_fixed_plan_simultaneous_segment_certificate
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hOldStrong
      target i hTarget reduced hPlan hProduces
  exact attachedSelectedPicture_standard_contained_replacement_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwo hOldStrong hCoreStrong K hAccept hLinear hn
    hOrder hOldSupreme i
    (cyclicExpandReducedPieces owner (by omega) reduced CoreActual CoreWagon)
    hInc hGeom hFresh hContained

end ActualSimultaneousSegmentTransfer
end StructuralRamsey.Girth
