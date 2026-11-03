import Girth.TrainActualPositiveCutLongWagonExisting
import Girth.TrainActualReducedCutFreshness
import Mathlib.Tactic

/-!
# Path A: a globally chosen nonadjacent long piece reuses an uncut source wagon

For a genuine selected supreme plan, its long wagon is fresh at every
retained original cut connector. Conversely, A3 on an acceptable source
cycle forces the wagon of a long piece spanning nonadjacent ORIGINAL cut
connectors to be an existing source wagon. Thus an old wagon exists, but
its position is NOT a cut. This is a physical obstruction to naive
fresh-wagon replacement of a non-singleton owner segment.

The supplementary A2 lemma records the only two possible orientations
of distinct vertex contacts around an original wagon connector.

All hypotheses refer to the actual selected picture and actual reduced
plan; no abstract replacements, no appendix, no manuscript green marker.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Two DISTINCT vertex connectors contacting a wagon which already
occurs as a source connector must be the predecessor and successor
of its occurrence, in one of the two orientations. This is the
exact A2 classification, including cyclic wrap. -/
theorem BigCycle.old_wagon_distinct_contacts_straddle
    {n : ℕ} (K : D.BigCycle n) (hA2 : K.A2)
    (w : P) (t a b : Fin n)
    (hOld : K.connector t = Sum.inr w)
    (ha : K.InWagonAt w a)
    (hb : K.InWagonAt w b)
    (hab : a ≠ b) :
    (a = trainCyclicPred t ∧ b = cyclicSucc t) ∨
    (a = cyclicSucc t ∧ b = trainCyclicPred t) := by
  rcases hA2.1 t w hOld a ha with haPred | haSucc
  · rcases hA2.1 t w hOld b hb with hbPred | hbSucc
    · exact False.elim (hab (haPred.trans hbPred.symm))
    · exact Or.inl ⟨haPred, hbSucc⟩
  · rcases hA2.1 t w hOld b hb with hbPred | hbSucc
    · exact Or.inr ⟨haSucc, hbPred⟩
    · exact False.elim (hab (haSucc.trans hbSucc.symm))

end OrderOneData

universe u v
section ChosenNonadjacentLong

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- If the two original cut connectors of a chosen reduced long piece
are nonadjacent in BOTH cyclic directions, its wagon equals a genuine
original wagon connector at a NON-CUT position. In particular it is
not eligible for the singleton fresh-wagon insertion theorem.

The plan and freshness come from the SAME actual HasSupremeAt witness;
the source A3 contacts are those of the SAME chosen long piece. -/
theorem attachedSelectedPicture_chosen_nonadjacent_long_old_uncut_wagon
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target)
    (hNotNext : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)))
    (hNotPrevious : cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
      cyclicSucc (cyclicOwnerCutIndex owner cut)) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∃ t : Fin n, K.connector t = Sum.inr (CoreWagon w) ∧
          t ∉ cyclicOwnerCutPositions owner) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hFreshCut⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_at_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target hSupreme
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
  obtain ⟨t, hOld⟩ :=
    attachedSelectedPicture_long_cut_piece_wagon_is_old_connector
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hCuts target cut first second w hLong
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))
      (cyclicOwnerCutIndex owner cut)
      rfl rfl hNotNext hNotPrevious
  refine ⟨t, hOld, ?_⟩
  intro hCut
  obtain ⟨j, hj⟩ := (cyclicOwnerCutIndex_mem_iff owner t).mp hCut
  exact (hFreshCut cut first second w hp j)
    (by simpa only [hj] using hOld)

end ChosenNonadjacentLong
end StructuralRamsey.Girth
