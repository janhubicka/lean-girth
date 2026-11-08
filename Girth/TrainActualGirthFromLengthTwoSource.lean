import Girth.TrainActualTwoCutThreeLeFullSupreme
import Girth.TrainActualSupremeResidualClosure
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Track A: FULL output system girth now reduces to original source LENGTH TWO

The merged exact-two-cut closure theorem already handles zero and
>=3 owner cuts. The new all-cases exactly-two-cut proof above handles
every ORIGINAL source cycle of length n>=3.

This short theorem combines those facts: full attached output
FullSystemGirthGT q follows from the real old SupremeCycleBound,
the real local witness FullSystemGirthGT and exact physical
linearity/strongness hypotheses, PROVIDED only that the original
source BigCycle of length EXACTLY TWO with exactly two owner
changes has a genuine global supreme plan.

This is the strongest currently justified *conditional* induction
interface. In particular it does NOT hide the length-two condition
or assert the full circulation forest theorem prematurely.
No appendix and no manuscript marker.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualGirthFromLengthTwoSource

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
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
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

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel





/-- Actual full selected attached-output system girth reduces
EXACTLY to original length-two source cycles with two geometric
owner cuts, provided the proved n>=3 case assembly is available.
The source length-two conclusion remains an honest hypothesis. -/
theorem attachedSelectedPicture_fullSystemGirth_of_length_two_two_cut
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hLengthTwo : ∀ (K : (Out).BigCycle 2),
      K.Acceptable →
      ∀ (owner : Fin 2 → I ⊕ CoreEdge),
      (∀ j, GeomAllowed (K.label j) (owner j)) →
      cyclicOwnerChanges owner = 2 →
      K.twiceOrder ≤ 2 * q →
      K.HasSimultaneousSupreme) :
    (Out).FullSystemGirthGT q := by
  apply attachedSelectedPicture_fullSystemGirth_of_two_cut_cases
    A hA B D C family selected e R f T U hShared hRel μ
    q hq hLinear hStrong hTwoCopies hOldStrong hCoreStrong
    hOldSupreme hWitness
  intro n K hAccept owner hAllowed hExactlyTwo hOrder
  by_cases hn2 : n = 2
  · subst n
    exact hLengthTwo K hAccept owner hAllowed hExactlyTwo hOrder
  · have hThree : 3 ≤ n := by
      have hMin := K.length_ge_two
      omega
    exact attachedSelectedPicture_two_cut_three_le_full_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hLinear hThree hOrder
      owner hAllowed hExactlyTwo hWitness hOldSupreme

end ActualGirthFromLengthTwoSource
end StructuralRamsey.Girth
