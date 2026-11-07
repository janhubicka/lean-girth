import Girth.TrainNoSingleCyclicOwnerCut
import Girth.TrainActualThreeCutFromFullSystem
import Girth.TrainActualZeroCutGlobalSupreme

set_option autoImplicit false
set_option Elab.async false

/-!
# Full attached output girth reduces to only the two-cut geometry

A genuine cyclic geometric owner word has zero changes or at least two.
At zero cuts, the checked old-picture GLOBAL simultaneous supreme
transfer gives the answer. Crucially, the already merged and kernel-audited
three-cut Path A theorem gives complete globally legal supremeness for
EVERY positive owner word with at least THREE changes. No rank induction
or replacement of original source B-labels by geometric owner indices
is needed in this case.

Therefore full attached-output SupremeCycleBound and FullSystemGirthGT
reduce to only TWO physical residual tasks:
* acceptable original BigCycles of exactly two occurrences;
* acceptable original BigCycles of at least three occurrences whose
  actual geometric owner assignment has EXACTLY two changes.

This is strictly simpler than the older conditional trichotomy/lexicographic
closure formulation. The theorem remains CONDITIONAL on both residual
physical cases, and on the real old/witness global system certificates
and the genuine strongness/two-A-edge inputs. These remain visible in
its statement. It neither proves the two-cut geometry nor constructs
the lower recursive witness or asserts high girth of an HJ power.

Every ambient physical A-edge and every distinct labelled wagon remains;
the appendix is unused.

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

/-- With REAL old and witness full-system certificates, only the
original length-two and EXACTLY-two-owner-cut physical cases remain.
In particular the ≥3-owner-cut case is already fully verified, so no
rank-descent oracle or global induction hypothesis appears here. -/
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
    (hTwoCycle : ∀ (K : (Out).BigCycle 2),
      K.Acceptable → K.twiceOrder ≤ 2 * q →
      K.HasSimultaneousSupreme)
    (hTwoCut : ∀ {n : ℕ} (K : (Out).BigCycle n)
      (hAccept : K.Acceptable) (hn : 3 ≤ n)
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
    · by_cases hn : 3 ≤ n
      · by_cases hExactlyTwo : cyclicOwnerChanges owner = 2
        · exact hTwoCut K hAccept hn owner hAllowed hExactlyTwo hOrder
        · have hThree : 3 ≤ cyclicOwnerChanges owner := by omega
          exact attachedSelectedPicture_three_cut_full_supreme_of_old_and_witness
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwo hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hThree
            hq hWitness hOldSupreme
      · have hLen : n = 2 := by
          have hMin := K.length_ge_two
          omega
        subst n
        exact hTwoCycle K hAccept hOrder
  exact ⟨hLinear, hSupreme⟩

end AttachedCycleExceptionalClosure

end StructuralRamsey.Girth
