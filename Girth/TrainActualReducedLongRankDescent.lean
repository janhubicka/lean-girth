import Girth.TrainActualLongOwnerRankBridge
import Girth.TrainActualSupremeChosenLongGlobal
import Girth.TrainActualLongStandardSupport
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

/-!
# Path A: genuine chosen reduced long pieces lower the actual minimal geometric rank

An actual reduced LongValid piece (in a designated supreme standard) has
two physical support edges whose entire carriers are contained in that
standard. If its original source boundary positions identify one isolated
occurrence and its wagon is fresh, the already checked physical insertion
constructs a genuine output BigCycle, preserving acceptability, numerical
order, and supreme pullback. The exact owner-word and designated-count
kernels then lower the MINIMUM geometric owner/designated lex rank.

A second theorem supplies the physical data from a globally chosen
supreme plan in the all-source-positions-cut case, conditional on the
chosen piece at the selected cut being long. This is not the full
cycle-transfer theorem: other kinds of selected pieces and two-cut
cycles are separate.

Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

/-- Consecutive retained cut connectors at consecutive ORIGINAL
positions certify that the intervening original occurrence is an
isolated geometric owner segment. Neither owner names nor minimality
are extra hypotheses. -/
theorem cyclicOwner_isolated_of_consecutive_cut_indices
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner) (hn : 2 ≤ n)
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos) :
    owner (trainCyclicPred pos) ≠ owner pos ∧
    owner pos ≠ owner (cyclicSucc pos) := by
  have hHere := cyclicOwnerCutIndex_is_change owner cut
  have hBefore :=
    cyclicOwnerCutIndex_is_change owner (trainCyclicPred cut)
  constructor
  · rw [hPrevious, cyclicSucc_trainCyclicPred_of_two_le hn pos]
      at hBefore
    exact hBefore
  · simpa only [hThis] using hHere

section ActualReducedLongGeometricRank

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
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- An ACTUAL reduced long piece chosen inside standard i, with a fresh
physical wagon and isolated source owner, produces a globally acceptable
actual output with strictly smaller minimum geometric/designated rank.
Both inserted physical edges are proved admissible from shared-support
carrier containment, not assumed to be old designated source labels. -/
theorem attachedSelectedPicture_fresh_long_minimal_designated_rank
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target cut : Fin (cyclicOwnerChanges owner))
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second)
    (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos)
    (hFresh : ∀ t : Fin n,
      K.connector t ≠ Sum.inr (CoreWagon w)) :
    ∃ outLength : ℕ, ∃ H : (Out).BigCycle outLength,
      List.ofFn (fun k : Fin outLength =>
        (H.label k, H.connector k)) =
        K.resultWord Out
          (K.onlyLongPieces Out pos (CoreActual first)
            (CoreWagon w) (CoreActual second)) ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
        ∃ kK : Fin n, K.label kK = H.label kH ∧
          K.HasSupremeAt Out kK) ∧
      ∃ minimumOwner : Fin outLength → I ⊕ CoreEdge,
        (∀ k, GeomAllowed (H.label k) (minimumOwner k)) ∧
        (∀ other : Fin outLength → I ⊕ CoreEdge,
          (∀ k, GeomAllowed (H.label k) (other k)) →
          cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
        Prod.Lex (· < ·) (· < ·)
          (cyclicOwnerChanges minimumOwner,
            H.designatedOccurrenceCount Out)
          (cyclicOwnerChanges owner,
            K.designatedOccurrenceCount Out) := by
  classical
  obtain ⟨hPrev, hNext⟩ :=
    cyclicOwner_isolated_of_consecutive_cut_indices
      owner (by omega) hCuts cut pos hThis hPrevious
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hSupports :
      (CoreActual first).1 ⊆ copyCarrier (Std i) ∧
      (CoreActual second).1 ⊆ copyCarrier (Std i) :=
    sharedWitness_long_piece_physical_edges_in_standard
      A hA D C e R f U μ Z target cut first second w
      hLong i hTarget
  have hFirst : GeomAllowed (Sum.inr (CoreActual first))
      (Sum.inl i) := by
    change (CoreActual first).1 ⊆ copyCarrier (Std i)
    exact hSupports.1
  have hSecond : GeomAllowed (Sum.inr (CoreActual second))
      (Sum.inl i) := by
    change (CoreActual second).1 ⊆ copyCarrier (Std i)
    exact hSupports.2
  have hPhysical : K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) :=
    attachedSelectedPicture_reduced_long_piece_physical_output
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hActive
      target cut first second w hLong pos hThis hPrevious
  obtain ⟨outLength, H, hWord, hOutAccept, hOutOrder, hPull⟩ :=
    attachedSelectedPicture_reduced_fresh_long_global_transfer
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hLinear hn owner hAllowed hCuts hActive
      target cut first second w hLong pos hThis hPrevious hFresh
  obtain ⟨minimumOwner, hMinAllowed, hMin, hRank⟩ :=
    K.oneFreshPhysicalLong_minimal_rank_of_isolated
      Out H (by omega) pos (CoreActual first)
      (CoreWagon w) (CoreActual second)
      owner (Sum.inl i) GeomAllowed
      hAllowed hFirst hSecond hPrev hNext hPhysical hWord
  exact ⟨outLength, H, hWord, hOutAccept, hOutOrder,
    hPull, minimumOwner, hMinAllowed, hMin, hRank⟩

/-- A globally CHOSEN legal supreme plan with all original owner
positions retained as cuts enjoys the same descending rank whenever
the chosen piece at the selected reduced cut is long. The plan,
legality, chosen piece, full freshness and exact cut alignment are
obtained from the already-checked actual geometric objects. -/
theorem attachedSelectedPicture_all_cuts_chosen_long_rank
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hEveryCut : ∀ k : Fin n, owner k ≠ owner (cyclicSucc k))
    (hActive : AStrong A C.toRelStructure S)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target)
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∃ outLength : ℕ, ∃ H : (Out).BigCycle outLength,
          H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
          (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
            ∃ kK : Fin n, K.label kK = H.label kH ∧
              K.HasSupremeAt Out kK) ∧
          ∃ minimumOwner : Fin outLength → I ⊕ CoreEdge,
            (∀ k, GeomAllowed (H.label k) (minimumOwner k)) ∧
            (∀ other : Fin outLength → I ⊕ CoreEdge,
              (∀ k, GeomAllowed (H.label k) (other k)) →
              cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
            Prod.Lex (· < ·) (· < ·)
              (cyclicOwnerChanges minimumOwner,
                H.designatedOccurrenceCount Out)
              (cyclicOwnerChanges owner,
                K.designatedOccurrenceCount Out)) := by
  classical
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hFresh⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_of_all_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hEveryCut target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro first second w hp
  have hDifferent : Z.label cut ≠ Z.label target := by
    intro heq
    have hKeep := (hPlan cut).1 heq
    have hImpossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hKeep
    cases hImpossible
  have hLong : Z.LongValid Wit target cut first w second := by
    have hCase := (hPlan cut).2 hDifferent
    simpa only [hp] using hCase
  let pos := cyclicOwnerCutIndex owner cut
  have hn2 : 2 ≤ n := by omega
  have hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos :=
    cyclicOwnerCutIndex_pred_of_every_cut
      owner hn2 hEveryCut cut
  obtain ⟨outLength, H, _hWord, hOutAccept, hOrder,
    hPull, minOwner, hMinAllowed, hMin, hRank⟩ :=
    attachedSelectedPicture_fresh_long_minimal_designated_rank
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hLinear hn owner hAllowed hCuts hActive
      target cut i hTarget first second w hLong
      pos rfl hPrevious
      (hFresh cut first second w hp)
  exact ⟨outLength, H, hOutAccept, hOrder,
    hPull, minOwner, hMinAllowed, hMin, hRank⟩

end ActualReducedLongGeometricRank
end StructuralRamsey.Girth
