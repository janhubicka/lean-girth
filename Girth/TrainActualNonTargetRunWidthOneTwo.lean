import Girth.TrainActualReducedShortSingleton
import Girth.TrainActualChosenTwoStepLong

/-!
# Path A: non-target owner runs have width one or two

For at least three owner cuts, the selected supreme plan has no short
piece at a non-singleton run. An actual long piece spanning a
non-singleton run forces an old uncut wagon between two original cuts.
We apply both results to the SAME chosen plan, not unrelated witnesses.
No appendix; no claim of global one-pass replacement.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure
universe u v
section NonTargetRunWidthOneOrTwo

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

/-- Every non-target run in the actual chosen reduced witness has
either adjacent original cut connectors or exactly one intermediate
uncut wagon connector. The second case entails two source steps. -/
theorem attachedSelectedPicture_nontarget_run_one_or_two_steps
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (hDifferent : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label cut ≠
      (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target) :
    (cyclicOwnerCutIndex owner cut =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) ∨
    (∃ t : Fin n, ∃ w : Quotient (U.wagonSetoid μ),
      K.connector t = Sum.inr (CoreWagon w) ∧
      t ∉ cyclicOwnerCutPositions owner ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred t ∧
      cyclicOwnerCutIndex owner cut = cyclicSucc t) := by
  by_cases hSingleton :
      cyclicOwnerCutIndex owner cut =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))
  · exact Or.inl hSingleton
  · right
    obtain ⟨pieces, hPlan, _hProduces, hTwoStep⟩ :=
      attachedSelectedPicture_chosen_nonadjacent_long_exact_two_step
        A hA B D C family selected e R f T U hShared hRel μ
        K hAccept owner hAllowed hThree target cut
        hSupreme hSingleton
    obtain ⟨first, second, w, hPiece, _hLong⟩ :=
      attachedSelectedPicture_any_plan_nontarget_nonsingleton_is_long
        A hA B D C family selected e R f T U hShared hRel μ
        K hAccept owner hAllowed hThree target cut pieces
        hPlan hDifferent hSingleton
    obtain ⟨t, hOld, hUncut, hPrev, hNext⟩ :=
      hTwoStep first second w hPiece
    exact ⟨t, w, hOld, hUncut, hPrev, hNext⟩

end NonTargetRunWidthOneOrTwo
end StructuralRamsey.Girth
