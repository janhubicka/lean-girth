import Girth.TrainActualThreeCutOnePassSupreme
import Girth.TrainActualPositiveCutChosenStandard
import Girth.TrainActualCutReductionDichotomy
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

/-!
# Path A: the complete three-or-more-owner-cut case

The actual geometric reduction has length equal to the number of owner
cuts. With at least three cuts, its twice-order is at least three, so
the exhaustive order-one / order-at-least-two dichotomy puts it in the
acceptable higher-order case (in fact twice-order is at least four).
Consequently the genuine witness FullSystemGirthGT supplies a globally
supreme reduced plan, without separately hypothesizing such a plan.

The checked one-pass expansion then transfers that SAME plan to a
globally legal simultaneous replacement of the original selected
picture cycle, under the explicit old supreme bound and strongness
hypotheses. No assumption on designated neighbor labels is required.

The TWO-CUT/order-one geometric-reduction case and the existence of
the actual recursive lower witness are not concluded by this module.
No axiom, sorry, support pruning, or synthetic designated-source label.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ThreeCutFromFullSystem

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
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- A positive-cut geometric reduction with at least three actual owner
cuts cannot be the order-one bridge exception. Its reduced cycle is
acceptable, and the genuine witness system-girth bound provides a
complete simultaneous supreme plan at the reduced level. -/
theorem attachedSelectedPicture_three_cut_reduced_supreme_of_fullSystem
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨hBounds, hCases, hAcceptAbove, _hBridges⟩ :=
    attachedSelectedPicture_geometric_cut_reduction_dichotomy
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hAccept hq hWitness
  have hLength : cyclicOwnerChanges owner ≤ Z.twiceOrder :=
    OrderOneData.BigCycle.length_le_twiceOrder Wit Z
  have hAbove : 4 ≤ Z.twiceOrder := by
    rcases hCases with hOne | hAbove
    · omega
    · exact hAbove
  have hReducedAccept : Z.Acceptable := hAcceptAbove hAbove
  have hReducedOrder : Z.twiceOrder ≤ 2 * q :=
    (hBounds.2.1).trans hOrder
  exact hWitness.2 _ Z hReducedAccept hReducedOrder

/-- Full three-or-more-owner-cut Path A transfer: the genuine witness
system-girth bound and old standard supreme bound yield simultaneous
supremeness on the actual original selected output cycle. No chosen
reduced target is a hypothesis, and no lexicographic decrease is needed
in this case. The two-cut reduction is a separate open case. -/
theorem attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness
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
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hq : 1 ≤ q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hReduced :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).HasSimultaneousSupreme :=
    attachedSelectedPicture_three_cut_reduced_supreme_of_fullSystem
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hThree hq hWitness hOrder
  obtain ⟨i, target, hOwner, hAt⟩ :=
    attachedSelectedPicture_cut_supreme_selects_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hReduced
  have hTarget :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).label target = Sum.inl i := by
    change owner (cyclicOwnerCutIndex owner target) = Sum.inl i
    exact hOwner
  exact attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwo hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hThree target i hTarget hAt hOldSupreme

end ThreeCutFromFullSystem
end StructuralRamsey.Girth
