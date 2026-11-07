import Girth.TrainNoSingleCyclicOwnerCut
import Girth.TrainActualThreeCutFromFullSystem
import Girth.TrainActualZeroCutGlobalSupreme

set_option autoImplicit false
set_option Elab.async false

/-!
# Full attached output girth reduces to exactly two geometric owner cuts

Every genuine finite cyclic owner word has zero changes or at least
two. The canonical indexed cut map injects its cut positions into all
source positions, so its change count can NEVER exceed cycle length.

At zero cuts the checked old-picture GLOBAL supreme-plan transfer
applies. For at least three changes the merged three-cut Path A theorem
gives a complete globally legal simultaneous supreme plan (using the
real witness FullSystemGirthGT, old standard SupremeCycleBound and
physical A-strongness). Thus the ONLY residual geometric assumption
needed to prove FULL output FullSystemGirthGT is the EXACTLY-two-cut
case, for original cycles of ANY length, including length two.

This replaces the older lexicographic-residual formulation and avoids
even a separate length-two exceptional hypothesis. The theorem is
CONDITIONAL on the actual two-cut geometry, not an unconditional proof
of the forest-partite theorem. It preserves all physical A-edges and
distinct quotient wagon labels, assumes no high girth of the HJ power,
and uses no appendix.

-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section AttachedCycleExceptionalClosure

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
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

/-- Under real old and witness full-system certificates, complete
output system girth follows from the exactly-two-geometric-owner-cut
case alone. No separate source length-two premise or rank-descent
oracle is assumed: zero and ≥3 cuts are already fully verified. -/
theorem attachedSelectedPicture_fullSystemGirth_of_two_cut_cases
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ r : Selected, ∃ x y : OldEdge,
      x ≠ y ∧ x.1 ⊆ copyCarrier r.1.embedding ∧
        y.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hTwoCut : ∀ {n : ℕ} (K : (Out).BigCycle n)
      (hAccept : K.Acceptable)
      (owner : Fin n → I ⊕ CoreEdge)
      (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
      (hExactlyTwo : cyclicOwnerChanges owner = 2)
      (hOrder : K.twiceOrder ≤ 2 * q),
      K.HasSimultaneousSupreme) :
    (Out).FullSystemGirthGT q := by
  have hSupreme : (Out).SupremeCycleBound q := by
    intro n K hAccept hOrder
    obtain ⟨owner, hAllowed, _hMinimal⟩ :=
      attachedSelectedPicture_cycle_exists_minimal_geometric_owners
        A hA B D C family selected e R f T U hShared μ K
    rcases cyclicOwnerChanges_zero_or_two_le K.length_ge_two owner with
      hZero | hPositive
    · exact attachedSelectedPicture_zero_cut_supreme_of_old_bound
        A hA B D C family selected e R f T U hShared hRel μ
        hStrong hTwo hOldStrong hCoreStrong
        K hAccept hOldSupreme hOrder owner hAllowed hZero
    · by_cases hExactlyTwo : cyclicOwnerChanges owner = 2
      · exact hTwoCut K hAccept owner hAllowed hExactlyTwo hOrder
      · have hThree : 3 ≤ cyclicOwnerChanges owner := by omega
        have hCountBound : cyclicOwnerChanges owner ≤ n := by
          have hCard :
              Fintype.card (Fin (cyclicOwnerChanges owner)) ≤
                Fintype.card (Fin n) :=
            Fintype.card_le_of_injective
              (cyclicOwnerCutIndex owner)
              (cyclicOwnerCutIndex owner).injective
          simpa using hCard
        have hn : 3 ≤ n := by omega
        exact attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness
          A hA B D C family selected e R f T U hShared hRel μ
          hStrong hTwo hOldStrong hCoreStrong
          K hAccept hLinear hn hOrder owner hAllowed hThree
          hq hWitness hOldSupreme
  exact ⟨hLinear, hSupreme⟩

end AttachedCycleExceptionalClosure

end StructuralRamsey.Girth
